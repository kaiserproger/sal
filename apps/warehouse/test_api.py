"""Opt-in functional tests of the real native SAL/PostgreSQL application.

Run from the repository root:
  SAL_TEST_POSTGRES_SOCKET=/owned/socket/.s.PGSQL.5432 \
  SAL_TEST_POSTGRES_CONTAINER=owned-test-postgres \
  python3 apps/warehouse/test_api.py

SAL_COMPILER defaults to target/debug/sal; SAL_TEST_POSTGRES_USER defaults to
warehouse. The supplied container must be a deliberately owned test instance
with local trust authentication and permission to CREATE/DROP DATABASE. No
production helper, Python database driver, shared fixture database, or retry of
an application request is used. Every test request reaches the native binary.
"""

import concurrent.futures
import http.client
import json
import os
from pathlib import Path
import signal
import socket
import subprocess
import tempfile
import threading
import time
import unittest
import uuid


ROOT = Path(__file__).resolve().parents[2]
RED = "SKU-RED-M"
BLUE = "SKU-BLUE-L"
ZERO = "SKU-ZERO-42"
UNICODE = "SKU-ЁЖ-М"


def sql_literal(value):
    # Administrative fixture SQL only, sent to psql in the owned container.
    return "'" + value.replace("'", "''") + "'"


def sal_literal(value):
    return json.dumps(value, ensure_ascii=False)


class WarehouseApi(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = os.environ.get("SAL_TEST_POSTGRES_SOCKET")
        container = os.environ.get("SAL_TEST_POSTGRES_CONTAINER")
        if not path and not container:
            raise unittest.SkipTest("opt in with SAL_TEST_POSTGRES_SOCKET and SAL_TEST_POSTGRES_CONTAINER")
        if not path or not container:
            raise RuntimeError("both SAL_TEST_POSTGRES_SOCKET and SAL_TEST_POSTGRES_CONTAINER are required")
        if not Path(path).is_socket():
            raise RuntimeError("SAL_TEST_POSTGRES_SOCKET must name the host-visible PostgreSQL socket file")
        if len(os.fsencode(path)) > 107 or "\0" in path:
            raise RuntimeError("PostgreSQL socket path does not fit sockaddr_un")
        if container.startswith("-") or not container:
            raise RuntimeError("invalid owned test container name")
        cls.container = container
        cls.user = os.environ.get("SAL_TEST_POSTGRES_USER", "warehouse")
        cls.database = "sal_warehouse_test_" + uuid.uuid4().hex
        cls.process = None
        cls.temp = tempfile.TemporaryDirectory(prefix="sal-warehouse-api-")
        cls.addClassCleanup(cls.temp.cleanup)
        cls.directory = Path(cls.temp.name)
        cls.addClassCleanup(cls.drop_database)
        cls.psql("CREATE DATABASE " + cls.database + ";", database="postgres")
        cls.psql((ROOT / "apps/warehouse/sql/001_schema.sql").read_text())
        cls.psql((ROOT / "apps/warehouse/sql/002_seed.sql").read_text())

        # Inherit a bound listener instead of releasing an ephemeral port and
        # racing another process. Python never accepts or serves a connection.
        listener = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        cls.addClassCleanup(listener.close)
        listener.bind(("127.0.0.1", 0))
        listener.listen(64)
        cls.port = listener.getsockname()[1]
        source = cls.directory / "warehouse_functional.sal"
        source.write_text(
            'use ' + sal_literal(os.path.relpath(ROOT / "apps/warehouse/warehouse.sal", cls.directory)) + '.\n'
            'operation WarehouseDatabaseSocket:\n'
            '    returns Bytes.\n    body:\n'
            '        return bytes(' + sal_literal(path) + ').\n'
            'operation WarehouseDatabaseName:\n'
            '    returns Bytes.\n    body:\n'
            '        return bytes(' + sal_literal(cls.database) + ').\n'
            'operation WarehouseDatabaseUser:\n'
            '    returns Bytes.\n    body:\n'
            '        return bytes(' + sal_literal(cls.user) + ').\n'
            'operation Main:\n'
            '    returns i64.\n'
            '    effects: SystemCall, UnsafeMemory.\n'
            '    body:\n'
            '        let mapped = LinuxMapMemory(usize(2097152)).\n'
            '        if mapped < 0:\n'
            '            LinuxClose(' + str(listener.fileno()) + ').\n'
            '            return mapped.\n'
            '        return ServerServe(' + str(listener.fileno()) + ', usize(mapped), usize(2097152), 32).\n',
            encoding="utf-8",
        )
        compiler = Path(os.environ.get("SAL_COMPILER", str(ROOT / "target/debug/sal"))).resolve()
        build = subprocess.run(
            [str(compiler), "build-exe", str(source), "--out", str(cls.directory / "native")],
            cwd=ROOT, text=True, capture_output=True, timeout=120, check=False,
        )
        if build.returncode:
            raise RuntimeError("native SAL compilation failed:\n" + build.stdout + build.stderr)
        cls.server_log = (cls.directory / "server.log").open("wb")
        cls.addClassCleanup(cls.server_log.close)
        cls.process = subprocess.Popen(
            [str(cls.directory / "native/warehouse_functional")],
            cwd=ROOT, stdin=subprocess.DEVNULL, stdout=cls.server_log,
            stderr=subprocess.STDOUT, pass_fds=(listener.fileno(),), start_new_session=True,
        )
        cls.addClassCleanup(cls.stop_server)
        listener.close()
        # Readiness is a real stock query, never a replay of a mutation.
        deadline = time.monotonic() + 15
        last_error = None
        while time.monotonic() < deadline:
            if cls.process.poll() is not None:
                raise RuntimeError("native server exited during startup: " + cls.server_output())
            try:
                status, body = cls.request("/stock", {"warehouse_id": 1}, timeout=2)
                if status == 200:
                    break
                last_error = (status, body)
            except (OSError, http.client.HTTPException) as error:
                last_error = repr(error)
            time.sleep(0.05)
        else:
            raise RuntimeError("native server readiness failed: " + repr(last_error) + "\n" + cls.server_output())

    @classmethod
    def psql(cls, sql, database=None):
        result = subprocess.run(
            ["docker", "exec", "-i", cls.container, "psql", "-X", "-q", "-A", "-t",
             "-v", "ON_ERROR_STOP=1", "-U", cls.user, "-d", database or cls.database],
            input=sql, text=True, capture_output=True, timeout=30, check=False,
        )
        if result.returncode:
            raise RuntimeError("owned test database command failed:\n" + result.stdout + result.stderr)
        return result.stdout.strip()

    @classmethod
    def drop_database(cls):
        cls.psql("DROP DATABASE IF EXISTS " + cls.database + " WITH (FORCE);", database="postgres")

    @classmethod
    def stop_server(cls):
        # Kill this owned process group, including forked request children; no
        # process-name search, global kill, shared port, or other server is used.
        if cls.process is None:
            return
        try:
            os.killpg(cls.process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        try:
            cls.process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            os.killpg(cls.process.pid, signal.SIGKILL)
            cls.process.wait(timeout=5)

    @classmethod
    def server_output(cls):
        cls.server_log.flush()
        return (cls.directory / "server.log").read_text(errors="replace")

    @classmethod
    def request(cls, path, body, method="POST", timeout=12):
        payload = body if isinstance(body, bytes) else json.dumps(body, ensure_ascii=False).encode("utf-8")
        connection = http.client.HTTPConnection("127.0.0.1", cls.port, timeout=timeout)
        try:
            connection.request(method, path, body=payload, headers={"Content-Type": "application/json"})
            response = connection.getresponse()
            raw = response.read()
            if response.getheader("Content-Type") != "application/json":
                raise AssertionError("non-JSON application reply: " + repr(raw))
            if int(response.getheader("Content-Length")) != len(raw):
                raise AssertionError("wrong response Content-Length")
            return response.status, json.loads(raw)
        finally:
            connection.close()

    def setUp(self):
        self.assertIsNone(self.process.poll(), "native server is not running")
        # Reset only this class's unique database; never truncate shared tables.
        self.psql("""
            UPDATE warehouses SET name=CASE id
              WHEN 1 THEN 'Central warehouse' WHEN 2 THEN 'Outlet warehouse'
              ELSE 'Closed warehouse' END, available=(id<>3);
            DELETE FROM inventory WHERE item_id>=100;
            DELETE FROM items WHERE id>=100;
            UPDATE inventory SET reserved=0, quantity=CASE
              WHEN warehouse_id=1 AND item_id=1 THEN 10
              WHEN warehouse_id=1 AND item_id=2 THEN 5
              WHEN warehouse_id=1 AND item_id=3 THEN 0
              WHEN warehouse_id=1 AND item_id=4 THEN 7
              WHEN warehouse_id=2 AND item_id=1 THEN 3
              WHEN warehouse_id=2 AND item_id=2 THEN 2 ELSE 4 END;
        """)

    def stock(self, warehouse=1):
        status, body = self.request("/stock", {"warehouse_id": warehouse})
        self.assertEqual(status, 200, body)
        return body

    def assert_counts(self, code, quantity, reserved, warehouse=1):
        items = {item["code"]: item for item in self.stock(warehouse)["items"]}
        self.assertIn(code, items)
        item = items[code]
        self.assertEqual((item["quantity"], item["reserved"], item["available_quantity"]),
                         (quantity, reserved, quantity - reserved))

    def assert_error(self, path, body, status, code=None, method="POST"):
        actual_status, reply = self.request(path, body, method=method)
        self.assertEqual(actual_status, status, reply)
        self.assertEqual(set(reply), {"error"})
        self.assertEqual(set(reply["error"]), {"code"})
        if code is not None:
            self.assertEqual(reply["error"]["code"], code)

    def test_metadata_unicode_json_escaping_and_zero_stock(self):
        stock = self.stock()
        self.assertEqual(stock["warehouse"], {"id": 1, "name": "Central warehouse", "available": True})
        self.assertEqual([item["code"] for item in stock["items"]],
                         sorted([RED, BLUE, ZERO, UNICODE], key=lambda value: value.encode("utf-8")))
        items = {item["code"]: item for item in stock["items"]}
        self.assertEqual(items[BLUE]["name"], 'Blue "wind" jacket')
        self.assertEqual(items[UNICODE]["name"], "Куртка")
        self.assertEqual(items[UNICODE]["size"], "M")
        self.assert_counts(ZERO, 0, 0)
        name = 'Склад "A"\\north\n\t'
        code = 'quoted\"\\\n' + "' OR 1=1 -- Ё"
        size = 'M"\\\t'
        self.psql("UPDATE warehouses SET name=" + sql_literal(name) + " WHERE id=1;"
                  "INSERT INTO items(id,name,size,code) VALUES(100," + sql_literal(name) + "," +
                  sql_literal(size) + "," + sql_literal(code) + ");"
                  "INSERT INTO inventory(warehouse_id,item_id,quantity) VALUES(1,100,2);")
        stock = self.stock()
        self.assertEqual(stock["warehouse"]["name"], name)
        item = next(item for item in stock["items"] if item["code"] == code)
        self.assertEqual((item["name"], item["size"]), (name, size))
        self.assertEqual(self.request("/reserve", {"codes": [code]}), (200, {"warehouse_id": 1, "reserved": 1}))
        self.assert_counts(code, 2, 1)
        self.assert_counts(RED, 10, 0)
        self.assertEqual(self.request("/release", {"codes": [code]})[0], 200)

    def test_arrays_are_atomic_and_missing_codes_do_not_mutate(self):
        self.assert_error("/reserve", {"codes": [RED, ZERO]}, 409, "insufficient_stock")
        self.assert_counts(RED, 10, 0)
        self.assert_error("/reserve", {"codes": [RED, "absent"]}, 404, "item_not_found")
        self.assert_counts(RED, 10, 0)
        self.assertEqual(self.request("/reserve", {"codes": [RED]}), (200, {"warehouse_id": 1, "reserved": 1}))
        self.assert_error("/release", {"codes": [RED, BLUE]}, 409, "insufficient_reservation")
        self.assert_counts(RED, 10, 1)
        self.assert_error("/release", {"codes": [RED, "absent"]}, 404, "item_not_found")
        self.assert_counts(RED, 10, 1)
        self.assertEqual(self.request("/release", {"codes": [RED]}), (200, {"warehouse_id": 1, "released": 1}))
        self.assert_counts(RED, 10, 0)

    def test_multiwarehouse_closed_and_empty_warehouses(self):
        self.assertEqual(self.request("/reserve", {"warehouse_id": 2, "codes": [RED, BLUE]}),
                         (200, {"warehouse_id": 2, "reserved": 2}))
        self.assert_counts(RED, 10, 0)
        self.assert_counts(RED, 3, 1, warehouse=2)
        self.assert_counts(BLUE, 2, 1, warehouse=2)
        self.assert_error("/reserve", {"warehouse_id": 2, "codes": [RED, UNICODE]}, 404, "item_not_found")
        self.assert_counts(RED, 3, 1, warehouse=2)
        self.assertEqual(self.request("/release", {"warehouse_id": 2, "codes": [BLUE, RED]}),
                         (200, {"warehouse_id": 2, "released": 2}))
        self.assert_counts(RED, 3, 0, warehouse=2)
        self.assert_error("/reserve", {"warehouse_id": 3, "codes": [RED]}, 409, "warehouse_unavailable")
        self.psql("UPDATE inventory SET reserved=1 WHERE warehouse_id=3 AND item_id=1;")
        self.assertEqual(self.request("/release", {"warehouse_id": 3, "codes": [RED]})[0], 200)
        self.assertFalse(self.stock(3)["warehouse"]["available"])
        self.assert_counts(RED, 4, 0, warehouse=3)
        self.psql("INSERT INTO warehouses(id,name) VALUES(100,'Empty');")
        self.addCleanup(self.psql, "DELETE FROM warehouses WHERE id=100;")
        self.assertEqual(self.stock(100), {"warehouse": {"id": 100, "name": "Empty", "available": True}, "items": []})
        for path in ("/stock", "/reserve", "/release"):
            self.assert_error(path, {"warehouse_id": 99999, "codes": [RED]}, 404, "warehouse_not_found")

    def test_invalid_bodies_ids_duplicates_and_limits(self):
        invalid = [b"", b"[]", b"null", b"{} trailing", b'{"codes":["x",]}',
                   b'{"codes":["x"],"warehouse_id":1,"wareh\\u006fuse_id":2}',
                   b'{"codes":["SKU-RED-M","SKU-RED-\\u004d"]}',
                   b'{"codes":["SKU-RED-M"],"codes":["SKU-BLUE-L"]}',
                   b'{"codes":["x"],"unknown":[1,]}', b'{"codes":["\\ud800"]}',
                   b'{"codes":["\\u0000"]}', b'{"codes":["\xff"]}',
                   b'{"codes":["x"],"warehouse_id":1.0}',
                   b'{"codes":["x"],"warehouse_id":1e0}',
                   b'{"codes":["x"],"warehouse_id":9223372036854775808}']
        for body in invalid:
            with self.subTest(body=body):
                self.assert_error("/reserve", body, 400, "invalid_request")
        for value in (0, -1, 1.5, 1e20, "1", True, None):
            for path in ("/reserve", "/release", "/stock"):
                with self.subTest(value=value, path=path):
                    self.assert_error(path, {"warehouse_id": value, "codes": [RED]}, 400)
        for codes in ([], [RED, None], "not-array", [""], [RED, RED]):
            self.assert_error("/reserve", {"codes": codes}, 400)
        self.assert_error("/reserve", {}, 400)
        self.assert_error("/release", {}, 400)
        self.assert_error("/stock", {}, 400)
        self.assert_error("/reserve", {"codes": ["x" * 129]}, 413)
        self.assert_error("/reserve", {"codes": ["code-" + str(i) for i in range(65)]}, 413)
        self.assert_error("/stock", b" " * 65537, 413)
        self.assertEqual(self.request("/reserve", b'{"codes":["SKU-RED-M"],"wareh\\u006fuse_id":1,"nested":{"ok":[true,null,1e2]}}')[0], 200)
        self.assert_counts(RED, 10, 1)

    def test_full_64_code_batch_and_explicit_result_limit(self):
        self.psql("""
            INSERT INTO items(id,name,size,code)
              SELECT 100+i, 'Batch item', 'M', 'BATCH-' || i FROM generate_series(0,63) AS i;
            INSERT INTO inventory(warehouse_id,item_id,quantity)
              SELECT 1,100+i,1 FROM generate_series(0,63) AS i;
        """)
        codes = ["BATCH-" + str(index) for index in range(64)]
        self.assertEqual(self.request("/reserve", {"codes": codes}),
                         (200, {"warehouse_id": 1, "reserved": 64}))
        items = {item["code"]: item for item in self.stock()["items"]}
        for code in codes:
            self.assertEqual((items[code]["quantity"], items[code]["reserved"],
                              items[code]["available_quantity"]), (1, 1, 0))
        self.assertEqual(self.request("/release", {"codes": list(reversed(codes))}),
                         (200, {"warehouse_id": 1, "released": 64}))
        self.assertEqual(self.psql("SELECT sum(reserved) FROM inventory WHERE item_id>=100;"), "0")
        # Encoding doubles all these quotes. The full response exceeds the
        # two-MiB caller arena: it must be a complete 413 JSON reply, not a
        # truncated or partially emitted 200 stream.
        self.psql("""
            INSERT INTO items(id,name,size,code)
              SELECT 1000+i,repeat(chr(34),256),repeat(chr(34),64),
                     lpad(i::text,128,'x') FROM generate_series(0,2999) AS i;
            INSERT INTO inventory(warehouse_id,item_id,quantity)
              SELECT 1,1000+i,1 FROM generate_series(0,2999) AS i;
        """)
        self.assert_error("/stock", {"warehouse_id": 1}, 413, "result_too_large")

    def test_action_routing(self):
        self.assert_error("/unknown", {}, 404, "action_not_found")
        for path in ("/reserve", "/release", "/stock"):
            self.assert_error(path, {}, 405, "method_not_allowed", method="GET")

    def parallel(self, path, bodies):
        barrier = threading.Barrier(len(bodies), timeout=15)

        def invoke(body):
            barrier.wait()
            return self.request(path, body)

        with concurrent.futures.ThreadPoolExecutor(max_workers=len(bodies)) as pool:
            futures = [pool.submit(invoke, body) for body in bodies]
            return [future.result(timeout=25) for future in futures]

    def test_concurrent_single_code_exact_capacity_and_release(self):
        bodies = [{"codes": [RED]} for _ in range(32)]
        reserved = self.parallel("/reserve", bodies)
        self.assertEqual([status for status, _ in reserved].count(200), 10, reserved)
        self.assertEqual([status for status, _ in reserved].count(409), 22, reserved)
        for status, body in reserved:
            self.assertEqual(body, {"warehouse_id": 1, "reserved": 1} if status == 200 else
                             {"error": {"code": "insufficient_stock"}})
        self.assert_counts(RED, 10, 10)
        self.assert_counts(RED, 3, 0, warehouse=2)
        released = self.parallel("/release", bodies)
        self.assertEqual([status for status, _ in released].count(200), 10, released)
        self.assertEqual([status for status, _ in released].count(409), 22, released)
        for status, body in released:
            self.assertEqual(body, {"warehouse_id": 1, "released": 1} if status == 200 else
                             {"error": {"code": "insufficient_reservation"}})
        self.assert_counts(RED, 10, 0)

    def test_concurrent_opposite_order_arrays_are_atomic(self):
        bodies = [{"codes": [RED, BLUE] if index % 2 else [BLUE, RED]} for index in range(32)]
        reserved = self.parallel("/reserve", bodies)
        self.assertEqual([status for status, _ in reserved].count(200), 5, reserved)
        self.assertEqual([status for status, _ in reserved].count(409), 27, reserved)
        self.assert_counts(RED, 10, 5)
        self.assert_counts(BLUE, 5, 5)
        released = self.parallel("/release", bodies)
        self.assertEqual([status for status, _ in released].count(200), 5, released)
        self.assertEqual([status for status, _ in released].count(409), 27, released)
        self.assert_counts(RED, 10, 0)
        self.assert_counts(BLUE, 5, 0)


    def test_concurrent_warehouses_keep_independent_capacity(self):
        bodies = [{"warehouse_id": 1 if index % 2 else 2, "codes": [RED]}
                  for index in range(32)]
        reserved = self.parallel("/reserve", bodies)
        for warehouse, capacity in ((1, 10), (2, 3)):
            replies = [reply for request, reply in zip(bodies, reserved)
                       if request["warehouse_id"] == warehouse]
            self.assertEqual([status for status, _ in replies].count(200), capacity, replies)
            self.assertEqual([status for status, _ in replies].count(409), 16 - capacity, replies)
            self.assert_counts(RED, capacity, capacity, warehouse=warehouse)
        released = self.parallel("/release", bodies)
        for warehouse, capacity in ((1, 10), (2, 3)):
            replies = [reply for request, reply in zip(bodies, released)
                       if request["warehouse_id"] == warehouse]
            self.assertEqual([status for status, _ in replies].count(200), capacity, replies)
            self.assertEqual([status for status, _ in replies].count(409), 16 - capacity, replies)
            self.assert_counts(RED, capacity, 0, warehouse=warehouse)


if __name__ == "__main__":
    unittest.main(verbosity=2)

