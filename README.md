# SAL

SAL is a deterministic, statically checked language with one canonical source representation. Programs are written directly in `.sal`; there is no natural-language translation layer, model invocation or alias frontend.

## Build and run locally

Prerequisites: Rust/Cargo for building the bootstrap compiler, GNU `as`, `ld`, and `ar` for native artifacts. The native target is Linux x86-64. `cc`, `nm`, and `readelf` are also used by integration tests. There are no third-party Cargo dependencies.

```sh
cargo build --workspace
./target/debug/sal build-exe examples/native/hello.sal --out /tmp/sal-hello
/tmp/sal-hello/hello
# Hello, world!

./target/debug/sal build-exe examples/native/functions.sal --out /tmp/sal-functions
/tmp/sal-functions/functions
# {"answer": 42}
```

`build-exe` defaults to the **native** backend. It emits GNU assembly and uses `as`/`ld` at build time, not generated Rust or `rustc`. The resulting executable has its own entry point, direct Linux write/exit syscalls, no interpreter, no dynamic library imports, no libc, and no Rust runtime. The compiler itself is still implemented in Rust and uses its standard library; self-hosting has not been implemented.

Native execution supports lexical `let`/`let mut`, `set`, branches, fixed-frame `while` loops, nearest-loop `break`/`continue`, calls/recursion, procedures, and returns. Boolean `&&`/`||` short-circuit; `!` negates a bool. Both operands are statically checked even when one will not execute. Precedence, low to high: `||`, `&&`, equality, ordering, `+ -`, `* / %`, `!`, field/index access. Arithmetic and comparisons are typed; overflow, division by zero, signed MIN/−1 and invalid conversions trap instead of wrapping. Scalar types are signed/unsigned 8-, 16-, 32- and 64-bit integers, `usize`, `isize` and `bool`. `Text` is a UTF-8 span; `Bytes` is a distinct arbitrary-byte span. Span equality compares contents. A `while true` loop without a `break` of its own counts as diverging for return coverage. Unsupported constructs fail closed.

`Main() -> i64` supplies the Linux process exit status. `Main() -> Text` prints its result and a newline; a sole zero-parameter Text operation retains the hello-world fallback. Procedures omit `returns`, may fall through, and cannot be used as values.

`Character` means one Unicode scalar; `Word` is nonempty text without Unicode whitespace; `Text` is unrestricted text. The body checker validates constrained literal construction and types of parameters, locals, calls, conditions, returns, field/index access, and return coverage. Native lowering of `Character` and `Word` is not yet available; they are **not** silently erased to unconstrained strings.

## Declarative operation contracts

Rules belong in the operation header next to `accepts` and `returns`, not in `if` chains inside the body:

```text
operation HttpMethod:
    accepts request of type Bytes.
    returns Bytes from request.
    requires:
        HttpRequestLineEnd(request) >= 0 otherwise bytes("").
    body:
        ...

operation Guarded:
    accepts owner of type i64.
    returns i64.
    requires:
        owner > 0 otherwise -1.
    ensures:
        result >= owner.
    body:
        return owner + 1.
```

| Clause | Meaning |
|---|---|
| `requires: COND otherwise VALUE.` | Evaluated once, in declaration order, before the body. A false condition returns `VALUE`, which must have the declared return type. |
| `requires: COND.` | A false condition traps (`ud2`); there is no silent fallthrough. |
| `ensures: COND.` | Evaluated exactly once after the return expression. `result` names the returned value; a body local called `result` does not shadow it. A false condition traps. |
| `returns T from a, b.` | Declares which parameters the returned views/records may borrow from. The memory checker verifies this provenance; it is not trusted. |
| `borrows x.` | `x` is an exclusive borrow of the caller's owner. The call site borrows the original slot, so no alias is created. |
| `consumes x.` | The owned parameter is transferred to the callee; the caller cannot use it afterwards. |

Contract conditions and `otherwise` values must be pure. The compiler walks the actual callee graph, so a contract that calls a writer, a syscall or an unresolved operation is rejected (`DEC203`), even if the caller has the effect. Record constructors count as pure. The declaration pass lowers contracts to ordinary SAL before effect, type and ownership checks, so lowered contracts get the same checks as hand-written code.

## Typed JSON schemas

An entity with `encoding JSON.` is a typed wire schema. Defaults and validation rules are declared on it:

```text
entity MutationInput:
    encoding JSON.
    has warehouse_id of type i64.
    has codes of type TextList.
    defaults warehouse_id to 1.
    requires:
        warehouse_id > 0.
        len(codes) > 0.
        len(codes) <= 64 otherwise -28.
        TextListEachNonEmpty(codes).
        TextListEachAtMost(codes, usize(128)) otherwise -28.
        TextListNoNul(codes).
        TextListUnique(codes).
```

For each schema the compiler generates ordinary SAL operations:

| Operation | Contract |
|---|---|
| `TDecodeJson(input: Bytes, storage: MutBytes)` | Returns `{status, value: T, written, read_end}`. Trailing non-whitespace input is `-22`. |
| `TDecodeJsonAt(input: Bytes, start: usize, storage: MutBytes)` | The same, but following bytes are allowed, for nested values. |
| `TEncodeJson(value: T, target: MutBytes) -> i64` | Returns the bytes written, or a negative status. A result that does not fit is an error, never truncated output. |

- **Field types:** `i64`, `u64`, `bool`, `Text`, `TextList`, and acyclic nested JSON entities.
- **Status codes:** a missing required field, a duplicate field (compared after escape decoding) or malformed JSON is `-22`. A failed rule returns its `otherwise` status, or `-22` if it has none.
- **Unknown fields:** fully validated, then ignored.
- **Storage:** decoded `Text` and `TextList` values borrow the caller's `storage`; nothing is allocated per field.
- **Runtime:** parsing and encoding run in `stdlib/json_model.sal` and `stdlib/text_list.sal`. The compiler only derives the typed field dispatch.

## Safe memory and the machine boundary

Application code works with checked owners and loans, not raw addresses:

| Value | Operations |
|---|---|
| `Buffer` (affine owner) | `buffer(usize)` allocates, `buffer_drop(owner)` releases exactly once, `len(owner)`. Cannot be copied, cast, addressed or sent. |
| `MutBytes` (exclusive loan) | `borrow_mut(buffer, offset, length)`, `slice_mut(span, offset, length)`, `put(span, index, u8)`, `byte(span, index)`, `view(span) -> Bytes`, `borrow_end(span)`. |
| `Bytes` / `Text` (read-only views) | `slice`, `byte`, `len`, `bytes(text)`. `text(bytes)` validates UTF-8 and traps on invalid input. |
| `Borrow<T>` | `borrow(owner)` gives a scoped exclusive reference to an owner for helper calls. |
| `Vector<T>`, `Map<K,V>` | POD-only collections with explicit capacity. Lookups return `{found, value}`; a failed allocation leaves existing data intact. |

The memory checker tracks the provenance of every view, including views held in records and views returned through calls. It rejects:

- using a loan after `borrow_end`;
- dropping or moving an owner while a derived view is live;
- returning a view of a dead local;
- overlapping mutable loans;
- an owner that is not dropped or transferred on every path, including early returns (`MEM208`).

Sibling loans of one arena are allowed. Disjointness is proven at compile time where possible; otherwise a range check runs before the second loan is granted.

Every operation declares its direct and callee effects. `Pure` cannot be combined with other effects. Raw intrinsics (`syscall`, `address`, `bytes_at`, `load8`, `store8`, atomics) need `UnsafeMemory`. An `unsafe:` block grants `UnsafeMemory` to the statements inside it only; `SystemCall` still propagates, and type and ownership checks still apply. The standard library keeps raw code in narrow `unsafe:` blocks at the OS boundary, so its public operations, including channels and threads, need only `effects: SystemCall.` There is no hidden signal policy or managed scheduler.

| Intrinsics | Contract |
|---|---|
| `len`, `bytes`, `byte`, `slice` | Byte length, zero-copy Text-to-Bytes view, bounds-checked access and subspans. |
| `i8`…`i64`, `u8`…`u64`, `usize`, `isize` | Checked explicit integer conversions. |
| `wrapping_*`, `bit_*`, `shift_left`/`shift_right`, `bits_as` | Explicit same-width wrapping and bit operations. Shifts reject counts at or above the bit width. |
| `syscall(number,a,b,c,d,e,f)` | Seven machine-word arguments in Linux x86-64 registers; returns negative errno. Requires `SystemCall` and `UnsafeMemory`. |
| `size_of`, `align_of`, `offset_of` | Target-checked C-layout record geometry, evaluated at compile time. |

## SAL libraries

Top-level `use "relative.sal".` loads a source relative to the containing file. Dependencies are loaded transitively, once per canonical path; cycles and missing files are errors, and diagnostics name the original file. `use "std/http.sal".` selects the compiler's embedded SAL package, never a local shadow. Standard module paths cannot escape that namespace.

Every algorithm below is implemented in `.sal`; no foreign runtime is linked:

| Module | Contents |
|---|---|
| `bytes`, `text`, `binary`, `math`, `hash` | Search and prefixes, decimal parsing and formatting, UTF-8 iteration and slicing, big/little-endian integers and VarInt/VarLong, checked integer helpers, FNV-1a and CRC32/CRC32C. |
| `buffer`, `collections` | Allocator policy for `Buffer`, and `Vector`/`Map` storage, growth, hashing and probing. |
| `json`, `json_model`, `text_list` | Strict JSON validation and string codecs (depth limits, UTF-8, surrogates), the schema runtime, and BE32-framed UTF-8 lists. |
| `http`, `http_client`, `routing`, `server` | Bounded HTTP/1.x request framing (strict Content-Length, chunked requests rejected), a client, exact routing with captures and percent decoding, and a fork-per-request server. The server has a 32-child limit, socket timeouts, an explicit SIGPIPE policy and descriptor cleanup. |
| `postgres` | PostgreSQL v3 with trust authentication only: startup, parameterized Parse/Bind/Execute/Sync, validated DataRow views and SQLSTATE errors. No libpq. |
| `net`, `fs`, `time`, `linux/*` | TCP/UDP/poll, durable file operations, monotonic/wall clocks and sleep, and the raw syscall wrappers. |
| `concurrency` | Bounded and rendezvous channels, atomic multi-arm selection, futex synchronization and native threads. |

```sh
./target/debug/sal build-exe examples/native/binary_io.sal --out /tmp/sal-binary
/tmp/sal-binary/binary_io | od -An -tx1
# 41 00 ff 0a
```

These libraries use caller-owned buffers. No automatic cache-locality or throughput improvement is claimed.

## C ABI: exports, imports and record layouts

```text
operation Add:
    accepts a of type i64.
    accepts b of type i64.
    returns i64.
    exports "C" as "sal_add".
    body:
        return a + b.
```

```sh
./target/debug/sal build-lib examples/native/exports.sal --out /tmp/sal-exports
```

Produces `libexports.a` and `exports.h`. A C caller includes that header and links the archive. SAL function bodies compile to native machine code; they are not implemented by the C caller or a foreign library. C is only used by the compatibility tests.

The C boundary supports fixed-width scalar parameters/results, procedures and naturally aligned `layout "C".` records, including nested and by-value records. Linux x86-64 SysV lowering covers register/stack arguments, aggregate register rollback and hidden large-record return pointers. C exports must remain pure; Text/Bytes cannot cross this boundary. `size_of(Record)`, `align_of(Record)` and `offset_of(Record, "field")` are compile-time geometry queries. A record constructor is `Record(field1, field2)`; fields use `value.field`.

A bodyless operation with `imports "C" as "foreign_symbol".` declares an explicit import and must declare **both** `SystemCall` and `UnsafeMemory`; callers inherit these effects. Link its implementation with repeated `build-exe … --link object.o --link library.a` arguments. Importing foreign code is an explicit application choice, never how the SAL HTTP/JSON/database libraries are implemented. Typed raw pointers, callbacks, unions, packed layouts, variadics and general FFI ownership rules remain unsupported. Raw machineword addresses are unsafe, not checked pointers. Export/import symbols must be valid identifiers and unambiguous. Contracts on exported operations are lowered into the exported body like any other contract; non-boolean conditions and unimplemented effects are rejected.

## Native HTTP declaration frontend

```sh
./target/debug/sal build-exe examples/native/tupoi.sal --out /tmp/tupoi
/tmp/tupoi/tupoi
# In another terminal:
curl http://127.0.0.1:8081/say/hello
# hello
```

Server/route declarations lower to ordinary SAL operations calling the libraries above. TupoiServer's GET echo is native, including percent decoding, UTF-8 checks and byte-exact response lengths; query text is excluded from the capture. Responses close the connection. Unknown methods/paths return 404; malformed selected captures return 400. Route-name order determines overlapping-route precedence; repeated capture names select the last matching segment. Original declarations are validated before lowering, and user-defined entry points are never silently replaced.

`--backend rust-std` explicitly selects the older Rust/std HTTP demonstration instead. It is not SAL stdlib and does not satisfy the foreign-runtime-free application requirement. Native builds never fall back to it.

`emit-rust` is the older declaration/scaffold generator: its unimplemented service/operation bodies are not executable SAL contracts. `verify --rust` checks a limited marked-file/import policy; it is not a whole-program architecture, effect, or FFI verifier. No Rust files or no marked files is a verification error; missing markers are warnings and fail under `--strict`.

## Cache-layout measurement

`examples/native/cache_layout.sal` compares one identical runtime-stride hot-field kernel over a two-byte dense record and a naturally aligned 16-byte C-layout record with cold data. Both perform the same 1,073,741,824 measured record visits after initialization and two warmups, with checksum `548145201152`. Allocation, initialization and output are outside timing/counter gates; no foreign benchmark runtime is used.

Observed on Ryzen 5 7535HS, 16-MiB L3, CPU 10, perf 7.0.14; four runs per layout in `d,a,a,d,d,a,a,d` order, 100% counter running time:

| Metric | Dense hot fields | Wider record |
|---|---:|---:|
| Record stride, bytes | 2 | 16 |
| Mapping, MiB | 256 | 2048 |
| Median instructions, billions | 83.285 | 83.293 |
| Median `cache-references`, millions | 85.712 | 562.821 |
| Median `cache-misses`, millions | 7.213 | 17.040 |
| Median measured time, seconds | 6.650 | 7.444 |
| Minimum measured time, seconds | 5.603 | 5.766 |
| Maximum measured time, seconds | 9.373 | 9.902 |

The footprints and observed cache-event counts differ substantially; elapsed ranges overlap. Other host activity caused swap traffic during the window, although the benchmark's memory-capped scope prohibited swapping its pages. This is **not a stable speedup claim**, an automatic compiler optimization, or evidence of warehouse throughput. Generic perf cache events are hardware-specific, not assumed to be one particular cache level.

```sh
target/debug/sal build-exe examples/native/cache_layout.sal --out /tmp/sal-cache
printf dst | /tmp/sal-cache/cache_layout
printf ast | /tmp/sal-cache/cache_layout
# Small correctness cases: checksum_sum=261376, exit 0.
printf dlt | taskset -c 10 /tmp/sal-cache/cache_layout
printf alt | taskset -c 10 /tmp/sal-cache/cache_layout
# Large clock-only cases; select an available CPU and leave its sibling idle.
```

For counters, create control/ack FIFOs and run `perf stat --delay=-1 --control=fifo:CONTROL,ACK -e cycles,instructions,cache-references,cache-misses,page-faults -- taskset -c CPU …`; the child must open CONTROL as fd 3 and ACK as fd 4 before exec, and receive `dlp`/`alp` on stdin. The SAL program enables counters only after warmup and disables them before output, consuming perf's complete NUL-terminated acknowledgement. Keep workloads/toolchain/affinity identical, avoid competing builds and swapping, inspect event multiplexing, and compare multiple interleaved runs rather than whole-process startup time.

## Channels and `wait_for`

Import `use "std/concurrency.sal".` and declare `effects: SystemCall.` on operations using this API and their callers.

| Operation | Contract |
|---|---|
| `channel(T, usize(capacity))` | `Channel<T>`; zero capacity is rendezvous, positive capacity is a bounded FIFO. |
| `channel_clone(ch)` / `channel_drop(ch)` | Explicitly duplicate / consume a channel owner. |
| `send(ch, value)` | `SendResult<T>{sent:bool, value:T}`; a closed channel returns `sent == false`, retaining the value. |
| `receive(ch)` | `ReceiveResult<T>{open:bool, value:T}`; drains buffered values after close, then returns `open == false` and a zero value. |
| `close(ch)` | Borrows the handle; first close returns true, subsequent closes false. Wakes blocked senders and receivers. |
| `spawn(Worker, value)` / `join(thread)` | A real OS thread and `Thread<i64>`; Worker takes one sendable value or owned channel and returns `i64`. Join consumes the thread. |
| `wait_for(receive(data), send(out, value), timeout(usize(ms)))` | Atomically commits one of 1–32 heterogeneous communication arms. One optional trailing `timeout` or `otherwise()` fallback; never both. |

Channels carry integer/bool values or recursively plain C-layout records, not borrowed Text/Bytes or nested handles. Channel/thread ownership is checked before lowering: no implicit aliases, reassignment, reuse after transfer, lost owners on an early exit, or double join. Ordinary typed calls can transfer owners; `spawn(Worker, channel_clone(ch))` transfers the explicit duplicate. Borrowing operations require bound channel variables and protect their lifetimes across **all** operand evaluations. General raw-memory escape/lifetime safety remains the caller's responsibility.

`WaitResult<T0,T1,...>` exposes `index`, `status` and typed `arm0`, `arm1`, … fields. Status is `0` for communication, `1` for closed, `2` for fallback; fallback index equals the communication-arm count. Each arm has `{selected:bool, open:bool, value:T}`. Only the winner is selected; only a successful winner is open. Unchosen/closed receive values are zeroed; send-arm values remain available. Operands are evaluated once, losing arms are deregistered before return, and no losing send is committed. Timeout zero is an immediate fallback if no arm is ready.

Arbitration uses a process-wide futex mutex and a rotating starting ticket for multi-arm waits; this avoids a fixed source-order preference, not OS-scheduling starvation. Waiting uses kernel futex blocking, not polling or a language scheduler. Each worker has an eight-MiB stack with a guard page, reclaimed on join. Allocation/spawn failure terminates nonzero; checked worker traps terminate the process rather than masquerading as a zero result. This is Linux x86-64 support, not a portable threading ABI.

```sh
target/debug/sal build-exe crates/sal_cli/tests/fixtures/concurrency/cancel_heterogeneous.sal \
  --strict --out /tmp/sal-select
/tmp/sal-select/cancel_heterogeneous
# Exit 0: typed record/bool readiness, cancellation and fallback.
```

## Warehouse API

`apps/warehouse/{codec,warehouse}.sal` implement the Lamoda task in SAL: three JSON RPC-like POST actions backed by PostgreSQL. Request and reply bodies are JSON schemas (`MutationInput`, `StockInput`, `ReserveReply`, `StockItem`, `ErrorReply`, …). Limits and status mappings are header `requires … otherwise` clauses, and the PostgreSQL wire format is handled in `std/postgres`. The application and readiness probe are native ELF binaries; the final scratch image contains no Rust, libc, Python, shell or database client. PostgreSQL runs in a separate infrastructure container.

### Start, stop and test

Prerequisites: Docker Engine with Compose v2 and Make. The multi-stage Docker build obtains the pinned Rust bootstrap toolchain and PostgreSQL image; host Rust is not needed for `make up`.

```sh
make up
# API: http://127.0.0.1:8080
make logs
make stop
# Stops both containers; the named database volume is preserved.

make test
make integration-test
```

`make test` needs host Rust/Cargo and the native test tools listed above; it also builds and runs the SAL library fixtures and Solaris examples (`make stdlib-test`, `make solaris-test`). `make integration-test` starts a Compose project with a unique name and its own fresh volumes. It then runs `apps/warehouse/test_api.sal`, the functional suite written in SAL, as a scratch image sharing the app's network namespace and database socket. The suite makes real HTTP requests and sets up fixtures over SQL through the SAL PostgreSQL client. The persistent application database is never touched, and the project's volumes are removed afterwards.

`WAREHOUSE_PORT=18080 make up` changes the host port. The default bind is loopback; exposing it with `WAREHOUSE_BIND=0.0.0.0` requires your own firewall/authentication/TLS policy. This is a local development deployment: the PostgreSQL client currently supports **trust authentication only**, over the shared Unix socket, and PostgreSQL has no TCP listener. Do not expose or share that socket with untrusted processes. HTTP authentication, TLS, MD5/SCRAM and production secrets management are not implemented.

Do not stop an unrelated service to claim the default port. The integration test binds an ephemeral loopback port (`WAREHOUSE_PORT=0`), so it never conflicts with a running deployment.

Fresh database volumes run `apps/warehouse/sql/001_schema.sql` and `002_seed.sql` automatically. Existing volumes retain their state and are not reinitialized on restart. The schema has unique item codes, warehouse/item foreign keys and `0 <= reserved <= quantity` constraints. Seeds use `ON CONFLICT DO NOTHING` and do not reset reservations. A shared item can have independent inventory at multiple warehouses.

### Working requests and responses

The following sequence assumes a fresh seeded database. Each unique code reserves or releases **one unit**; a batch succeeds entirely or changes nothing. `warehouse_id` defaults to `1` for mutations and is required for stock.

```sh
curl -sS http://127.0.0.1:8080/reserve \
  -H 'Content-Type: application/json' \
  -d '{"warehouse_id":1,"codes":["SKU-RED-M","SKU-BLUE-L"]}'
# {"warehouse_id":1,"reserved":2}

curl -sS http://127.0.0.1:8080/release \
  -H 'Content-Type: application/json' \
  -d '{"codes":["SKU-RED-M","SKU-BLUE-L"]}'
# {"warehouse_id":1,"released":2}

curl -sS http://127.0.0.1:8080/stock \
  -H 'Content-Type: application/json' \
  -d '{"warehouse_id":1}'
```

Stock response after that reserve/release sequence (formatted for readability):

```json
{
  "warehouse": {"id": 1, "name": "Central warehouse", "available": true},
  "items": [
    {"name": "Blue \"wind\" jacket", "size": "L", "code": "SKU-BLUE-L", "quantity": 5, "reserved": 0, "available_quantity": 5},
    {"name": "Red shirt", "size": "M", "code": "SKU-RED-M", "quantity": 10, "reserved": 0, "available_quantity": 10},
    {"name": "Black shoes", "size": "42", "code": "SKU-ZERO-42", "quantity": 0, "reserved": 0, "available_quantity": 0},
    {"name": "Куртка", "size": "M", "code": "SKU-ЁЖ-М", "quantity": 7, "reserved": 0, "available_quantity": 7}
  ]
}
```

Warehouse `2` starts with three red shirts and two blue jackets; reservations there do not alter warehouse `1`. Warehouse `3` is unavailable for new reservations, but stock reads and release of an existing reservation remain permitted.

```sh
curl -sS http://127.0.0.1:8080/reserve \
  -H 'Content-Type: application/json' -d '{"codes":["SKU-ZERO-42"]}'
# HTTP 409: {"error":{"code":"insufficient_stock"}}
```

| HTTP | Error codes |
|---|---|
| 400 | `invalid_request`: malformed JSON/HTTP, invalid ID/code, duplicate recognized keys or decoded codes. |
| 404 | `action_not_found`, `warehouse_not_found`, `item_not_found`. |
| 405 | `method_not_allowed`: known action requested with a method other than POST. |
| 408 | `request_timeout`: incomplete request exceeds the socket read timeout. |
| 409 | `warehouse_unavailable`, `insufficient_stock`, `insufficient_reservation`. |
| 413 | `request_too_large`, `result_too_large`. |
| 431 | `headers_too_large`. |
| 503 | `database_error`, `commit_outcome_unknown`. |

Limits: JSON body 65,536 bytes; mutation batch 1–64 distinct codes; each decoded UTF-8 code 1–128 bytes without NUL; positive signed-64-bit warehouse ID. Field order and whitespace are arbitrary, escaped keys are recognized, and unknown fields are ignored only after validating their complete JSON value. Stock rows are sorted by code bytes. Responses are bounded by the caller's two-MiB request arena; an oversized result returns a complete 413 error, not truncated JSON. HTTP and database sockets have five-second I/O timeouts; the server admits at most 32 request children.

### Transactions and failure semantics

Request values travel in PostgreSQL Bind parameters, never SQL interpolation. Mutations lock warehouse metadata, then inventory rows in item-ID order, validate the entire batch and update inside one transaction. Consistent lock order prevents opposite-order code arrays from introducing a lock-order deadlock. Database constraints remain the final invariant. Stock uses a repeatable-read read-only transaction so metadata and quantities share a snapshot.

Responses report success only after COMMIT is acknowledged. A lost/malformed COMMIT reply returns `commit_outcome_unknown`: the write may have committed. There is deliberately no automatic replay or compensating release. Mutation requests are **not idempotent**; do not blindly retry after a lost HTTP response or ambiguous commit. The API does not identify an owning order/reservation token; release acts on the warehouse's aggregate reserved count.

The real PostgreSQL functional suite covers exact-capacity concurrent reserve/release, atomic opposite-order batches, independent warehouse capacities, all 64 codes, unavailable/missing warehouses, absent/out-of-stock items, JSON/Unicode/SQL-like strings, malformed inputs and oversized results.

## Verification

```sh
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
make stdlib-test solaris-test
readelf -lW /tmp/sal-hello/hello
readelf -dW /tmp/sal-hello/hello
```

Integration tests build and run native programs. They cover:

- mutation, loops, checked arithmetic and conversions;
- contracts and schemas;
- the memory checker's rejections and accepted patterns;
- binary memory/I/O and all seven syscall operands;
- source diamonds and cycles;
- HTTP framing, JSON/Unicode boundaries and PostgreSQL framing;
- channels and threads under stress;
- real C callers, and the runtime dependencies of the produced binaries.

Repeated builds with the same toolchain are checked; identical binaries across toolchains are not. Socket tests own their ephemeral listeners and use bounded cleanup and deadlines.

## Remaining language work

- The compiler is not self-hosted.
- `Character` and `Word` are not lowered natively.
- Borrowed spans cannot cross the C ABI or travel through channels.
- Raw `unsafe:` code is audited by hand, not proven safe.
