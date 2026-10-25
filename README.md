# Anglish and SAL

Anglish (`.ang`) is the human/agent-facing input language. SAL (`.sal`) is the deterministic compiler representation. Models may propose Anglish interpretations; they are not part of SAL compilation. A well-typed translation does **not** prove that a model preserved the user's intention: changing a requested port to another valid port must be caught by comparing the proposal with the request, not by a type checker.

One canonical representation per operation; frontend aliases lower to that representation. Current Anglish recognition is a small deterministic sentence classifier, not general natural-language understanding. No cloud access or model is needed for the supported sentences.

## Build and run locally

Prerequisites: Rust/Cargo for building the bootstrap compiler, GNU `as`, `ld`, and `ar` for native artifacts. The native target is Linux x86-64. `cc`, `nm`, and `readelf` are also used by integration tests. There are no third-party Cargo dependencies.

```sh
cargo build --workspace
./target/debug/sal build-exe --ang examples/ang/hello.ang --out /tmp/sal-hello
/tmp/sal-hello/hello
# Hello, world!

./target/debug/sal build-exe examples/native/functions.sal --out /tmp/sal-functions
/tmp/sal-functions/functions
# {"answer": 42}
```

`build-exe` defaults to the **native** backend. It emits GNU assembly and uses `as`/`ld` at build time, not generated Rust or `rustc`. The resulting executable has its own entry point, direct Linux write/exit syscalls, no interpreter, no dynamic library imports, no libc, and no Rust runtime. The compiler itself is still implemented in Rust and uses its standard library; self-hosting has not been implemented.

Native execution supports lexical `let`/`let mut`, `set`, branches, fixed-frame `while` loops, nearest-loop `break`/`continue`, calls/recursion, procedures, and returns. Boolean `&&`/`||` short-circuit; `!` negates a bool. Both operands are statically checked even when one will not execute. Precedence, low to high: `||`, `&&`, equality, ordering, `+ -`, `* / %`, `!`, field/index access. Arithmetic and comparisons are typed; overflow, division by zero, signed MIN/−1 and invalid conversions trap instead of wrapping. Scalar types are signed/unsigned 8-, 16-, 32- and 64-bit integers, `usize`, `isize` and `bool`. `Text` is a UTF-8 span; `Bytes` is a distinct arbitrary-byte span. Span equality compares contents. Unsupported constructs fail closed.

`Main() -> i64` supplies the Linux process exit status. `Main() -> Text` prints its result and a newline; a sole zero-parameter Text operation retains the hello-world fallback. Procedures omit `returns`, may fall through, and cannot be used as values.

`Character` means one Unicode scalar; `Word` is nonempty text without Unicode whitespace; `Text` is unrestricted text. The body checker validates constrained literal construction and types of parameters, locals, calls, conditions, returns, field/index access, and return coverage. Native lowering of `Character` and `Word` is not yet available; they are **not** silently erased to unconstrained strings.

## Anglish translation

```sh
./target/debug/sal run-ang examples/ang/hello.ang > /tmp/hello.sal
./target/debug/sal check /tmp/hello.sal
./target/debug/sal build-exe /tmp/hello.sal --out /tmp/from-sal
/tmp/from-sal/hello
```

`run-ang` translates; despite the historical command name, it does not execute the program. stdout contains structurally checked SAL; diagnostics go to stderr. The deterministic frontend remains the default.

### Optional model and omp bridge

`--model-command PROGRAM` selects an explicit Anglish proposal generator. Repeat `--model-arg ARG` for its arguments, including arguments beginning with `--`. The command receives the SAL grammar and Anglish input on stdin and must return only UTF-8 SAL on stdout. It is executed directly, not through a shell. Nonzero exit, malformed SAL and semantic errors fail the command; there is no deterministic fallback hiding a model failure.

For example, with an already configured omp provider:

```sh
printf '%s\n' 'Create Main returning Text with the exact result "Anglish model bridge".' > /tmp/model.ang
./target/debug/sal run-ang /tmp/model.ang \
  --model-command omp \
  --model-arg -p \
  --model-arg --model --model-arg opencode-go/muse-spark-1.3-contributor \
  --model-arg --no-tools --model-arg --no-lsp \
  --model-arg --no-extensions --model-arg --no-skills --model-arg --no-rules \
  --model-arg --no-session --model-arg --no-title \
  --model-arg --max-time --model-arg 90 \
  --model-arg --system-prompt \
  --model-arg 'Translate Anglish to SAL using the supplied grammar. Output SAL source only, no Markdown or commentary.' \
  > /tmp/model-proposal.sal
# Review the proposal against the request before compiling it.
./target/debug/sal build-exe /tmp/model-proposal.sal --out /tmp/model-program
/tmp/model-program/model-proposal
# Anglish model bridge
```

The same model options work with `build-exe --ang` and `build-lib --ang`, but never with SAL input. No model is invoked by ordinary SAL compilation. A local runner can implement the same stdin/stdout protocol; the selected runner owns provider credentials and whether input leaves the machine. This is an omp CLI bridge, not an omp plugin. Passing structural checks does **not** establish that a model preserved intent.

The supplied model grammar includes checked integer widths, short-circuit boolean operators, nearest-loop `break`/`continue`, C-layout records and explicit C imports/exports. Unsupported constructs must be reported rather than replaced with a different implementation.

## SAL libraries and machine boundary

Top-level `use "relative.sal".` loads a source relative to the containing file. Dependencies are loaded transitively once by canonical path; cycles and missing files are errors. Diagnostics identify the original dependency file. `use "std/http.sal".` selects the compiler's embedded SAL source package, never a local shadow or foreign runtime. Standard module paths cannot escape that namespace.

```text
use "std/bytes.sal".
operation Count:
    accepts data of type Bytes.
    returns usize.
    body:
        let mut count = usize(0).
        while count < len(data):
            set count = count + 1.
        return count.
```

Native intrinsics provide computation and the explicit OS boundary, not protocol implementations:

| Intrinsics | Contract |
|---|---|
| `len`, `bytes` | Byte length and zero-copy Text-to-Bytes view. |
| `byte`, `slice` | Bounds-checked byte access/subspans; empty endpoint slices are valid. |
| `i8`…`i64`, `u8`…`u64`, `usize`, `isize` | Checked explicit integer conversions. |
| `syscall(number,a,b,c,d,e,f)` | Exactly seven machineword arguments; Linux x86-64 registers, signed negative errno; requires **both** `SystemCall` and `UnsafeMemory`. |
| `address`, `bytes_at`, `load8`, `store8` | Explicit raw-memory escape/access; requires `UnsafeMemory`. |
| `size_of`, `align_of`, `offset_of` | Target-checked C-layout record geometry, evaluated at compile time. |

Every operation must declare its direct and callee effects. `Pure` cannot accompany another effect. Native lowering accepts implemented `SystemCall`/`UnsafeMemory` effects, not abstract promises. Raw memory operations do not provide ownership or mapping validity: the caller owns lifetime, bounds and alias discipline. Kernel signal behavior remains Linux behavior; there is no hidden signal policy or managed scheduler.

The following algorithms are actual `.sal` implementations:

- `stdlib/bytes.sal`: prefix/search, decimal parsing/formatting (including signed MIN), and bounded copying.
- `stdlib/linux/{io,memory,net}.sal`: partial-write/EINTR loops, exact reads, mappings, TCP and filesystem Unix sockets using explicit caller storage.
- `stdlib/http.sal`: bounded fragmented HTTP/1.0–1.1 request framing, strict Content-Length handling, method/path views, and JSON response headers/body writes. Chunked requests and duplicate Content-Length are rejected; responses close the connection.
- `stdlib/json.sal`: complete JSON value validation with depth limits, strict UTF-8 and surrogate handling, unsigned integers, and bounded string decoding/encoding. Writers may partially change their output buffer on an error; callers must not publish it as a successful result.
- `stdlib/routing.sal`: exact raw path matching/captures, query exclusion, strict percent decoding and UTF-8 validation.
- `stdlib/server.sal` and `stdlib/linux/process.sal`: bounded fork-per-request lifecycle, explicit SIGPIPE policy, socket timeouts, descriptor/mapping cleanup and child reaping. There is no language scheduler.
- `stdlib/postgres.sal`: trust-authenticated PostgreSQL v3 startup, bounded frame parsing, parameterized Parse/Bind/Execute/Sync, validated DataRow views and SQLSTATE errors. No libpq or database driver is linked.
- `stdlib/concurrency.sal`: bounded/rendezvous channels, atomic multi-arm selection, futex synchronization and native thread lifecycle. Compiler support supplies typed lowering and machine/OS intrinsics, not a foreign channel implementation.

```sh
./target/debug/sal build-exe examples/native/binary_io.sal --out /tmp/sal-binary
/tmp/sal-binary/binary_io | od -An -tx1
# 41 00 ff 0a
```

These libraries use caller-owned buffers, not a foreign allocator or Rust protocol templates. Kernel `timeval` and signal-action structures use typed C-layout records instead of hand-packed byte offsets. Early returns, short-circuit guards and loop control are language constructs rather than library-specific state-flag workarounds. Contiguous data access is possible; no automatic cache-locality or application throughput improvement is claimed.

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

A bodyless operation with `imports "C" as "foreign_symbol".` declares an explicit import and must declare **both** `SystemCall` and `UnsafeMemory`; callers inherit these effects. Link its implementation with repeated `build-exe … --link object.o --link library.a` arguments. Importing foreign code is an explicit application choice, never how the SAL HTTP/JSON/database libraries are implemented. Typed raw pointers, callbacks, unions, packed layouts, variadics and general FFI ownership rules remain unsupported. Raw machineword addresses are unsafe, not checked pointers. Export/import symbols must be valid identifiers and unambiguous. Textual pre/postconditions and unimplemented effects are rejected by native lowering rather than reported as enforced contracts.

## Native HTTP declaration frontend

```sh
./target/debug/sal build-exe --ang examples/ang/tupoi.ang --out /tmp/tupoi
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

Import `use "std/concurrency.sal".` and declare `effects: SystemCall, UnsafeMemory.` on operations using this API and their callers.

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

`apps/warehouse/{codec,warehouse}.sal` implement the Lamoda task in SAL: three JSON RPC-like POST actions backed by PostgreSQL. The application and readiness probe are native ELF binaries; the final scratch image contains no Rust, libc, Python, shell or database client. PostgreSQL is a separate infrastructure container. Python is used only by the functional test harness.

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

`make test` also needs host Rust/Cargo and the native test tools listed above. `make integration-test` starts the Compose services, builds the host compiler, then exercises an isolated temporary database through the real native HTTP application; it additionally needs Python 3. The test database is created and dropped explicitly, never substituted for the persistent application database.

`WAREHOUSE_PORT=18080 make up` changes the host port. The default bind is loopback; exposing it with `WAREHOUSE_BIND=0.0.0.0` requires your own firewall/authentication/TLS policy. This is a local development deployment: the PostgreSQL client currently supports **trust authentication only**, over the shared Unix socket, and PostgreSQL has no TCP listener. Do not expose or share that socket with untrusted processes. HTTP authentication, TLS, MD5/SCRAM and production secrets management are not implemented.

When using a different port, pass the same `WAREHOUSE_PORT` to `make integration-test` and substitute that port in the requests below. Do not stop an unrelated service to claim the default port.

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
readelf -lW /tmp/sal-hello/hello
readelf -dW /tmp/sal-hello/hello
```

Integration coverage builds and executes native programs, tests mutation/loops, checked arithmetic/conversions, binary memory/I/O and all seven syscall operands, resolves source diamonds/cycles, exercises HTTP framing and JSON/Unicode boundaries, links real C callers (including u8/Void), and inspects runtime dependencies. It checks repeated native builds with the same toolchain, not identical binaries across toolchains. Socket tests own their ephemeral listeners and use bounded cleanup/deadlines. The optional omp bridge was also exercised through real model translation, native compilation and execution.

## Remaining language work

General safe owned collections/borrowing and executable contracts beyond checked locals/spans and explicit unsafe memory access are **not implemented capabilities**. Channel/thread owner checking is deliberately narrower than a general borrow checker; it does not make raw memory access safe.
