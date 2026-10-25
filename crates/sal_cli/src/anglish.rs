//! Optional model proposals belong to Anglish, never to the SAL compiler.

use std::io::Write;
use std::process::{Command, Stdio};

use sal_syntax::Diagnostic;

const PROMPT: &str = r#"Translate the following Anglish requirements into SAL source. Output ONLY SAL source, without Markdown fences or commentary. Preserve the requested behavior, values and constraints. If the request cannot be represented faithfully, fail explicitly instead of inventing behavior.
SAL is line-based; indentation is spaces, comments start with #, statements end in a period and block headers end in a colon.
An operation has this canonical form:
operation Main:
    returns Text.
    body:
        return "Hello, world!".
Parameters: `accepts name of type i64.` before body. Native types: Text (UTF-8), Bytes (arbitrary immutable byte span), bool, i8/i16/i32/i64, u8/u16/u32/u64, usize, isize. A procedure omits returns and finishes by falling through its body; bare `return.` is not supported. Main() -> Text prints its result; Main() -> i64 returns the process exit status. Operations call each other as Name(arguments). Use `let name = expression.` for immutable locals, `let mut name = expression.` and `set name = expression.` for mutation. Control flow: `if condition:` / optional `else:`, `while condition:`, and `break.` / `continue.` for the nearest enclosing loop. Return is `return expression.`. Expression statements end in a period. Operators in increasing precedence: ||, &&, == !=, < <= > >=, + -, * / %, unary !, postfix calls/fields/indexing. && and || short-circuit; both operands must still type-check and declare effects. No implicit variable numeric casts or automatic allocation. Integer arithmetic and conversions are checked.
Primitives: len(Text|Bytes)->usize, bytes(Text)->Bytes, byte(Bytes,usize)->u8, slice(Bytes,usize,usize)->Bytes; integer type names are explicit checked conversions. Literals may take their expected parameter type. Strings support \\, \", \n, \r, \t, \u{HEX} escapes. `use "relative.sal".` loads a source relative to the containing source file; `use "std/bytes.sal".` loads the embedded SAL standard module. Standard modules include linux/io, linux/memory, linux/net, linux/process, bytes, json, http, routing, server and postgres (all with .sal). Do not invent absent library APIs.
Records: `entity Pair:` with indented `layout "C".` and `has x of type i64.` / `has y of type u16.` fields. Construct Pair(x, y) and access value.x. Only supported scalar and nested C-layout fields are allowed. size_of(Pair), align_of(Pair), offset_of(Pair, "y") are compile-time queries. A pure operation can declare `exports "C" as "symbol".`; a bodyless operation can declare `imports "C" as "symbol".` with both SystemCall and UnsafeMemory effects. Text/Bytes cannot cross the C boundary; linking foreign implementations is an explicit caller choice.
Unsafe primitives: syscall(number,a,b,c,d,e,f)->i64 is Linux x86-64, exactly seven machineword arguments; requires `effects: SystemCall, UnsafeMemory.` on the containing operation and every caller. address(Text|Bytes|scalar|record)->usize, bytes_at(usize,usize)->Bytes, load8(usize)->u8, store8(usize,u8)->Void require UnsafeMemory. Raw pointers require valid mappings and caller-managed lifetime/alias discipline. Safe byte indexing/slicing is checked. Do not invent foreign runtime calls or silently change required ports, data or effects. Executable contracts, floating point and other unsupported native constructs must not be substituted for executable implementation.
Concurrency: import `use "std/concurrency.sal".`; operations and callers declare SystemCall and UnsafeMemory. channel(T, usize(capacity))->Channel<T> (zero=rendezvous); channel_clone(ch) creates another owner; channel_drop(ch) consumes it. send(ch,value)->SendResult<T>{sent:bool,value:T}; receive(ch)->ReceiveResult<T>{open:bool,value:T}; close(ch)->bool closes once. T is an integer, bool or recursively plain C-layout record, never a span or nested handle. No implicit handle aliases/reassignment: all owners must be consumed on every exit. Borrow channel variables; do not borrow an unbound channel-producing call. spawn(Worker,value)->Thread<i64> runs an OS thread; Worker accepts one sendable value or owned Channel and returns i64. join(thread)->i64 consumes it. Typed operation arguments/returns can transfer owners; spawn(Worker,channel_clone(ch)) consumes the explicit duplicate. No managed scheduler.
wait_for(receive(data),send(out,value),timeout(usize(milliseconds))) accepts 1-32 heterogeneous communication arms and at most one trailing timeout or otherwise(). It returns WaitResult<T0,T1,...> with index:usize, status:usize (0 success,1 closed,2 fallback), and armN:WaitArm<TN>{selected:bool,open:bool,value:TN}. Only a winning successful arm is open; unchosen/closed receive values are zero, send values retained. Fallback index equals communication-arm count. All operands evaluate once and exactly one arm commits; a zero timeout does not block. Declare effects and explicitly join/drop remaining owners after selecting.
The model proposes source; structural/type validation does not prove preservation of intent.
Anglish input follows:
"#;

#[derive(Default)]
pub(crate) struct Model {
    program: Option<String>,
    arguments: Vec<String>,
}

impl Model {
    pub(crate) fn program(&mut self, value: String) {
        if value.is_empty() || self.program.replace(value).is_some() {
            crate::bad_args("--model-command requires one nonempty executable name".into());
        }
    }

    pub(crate) fn argument(&mut self, value: String) {
        self.arguments.push(value);
    }

    pub(crate) fn validate(&self) {
        if self.program.is_none() && !self.arguments.is_empty() {
            crate::bad_args("--model-arg requires --model-command".into());
        }
    }

    pub(crate) fn enabled(&self) -> bool {
        self.program.is_some()
    }

    pub(crate) fn translate(&self, input: &str) -> Result<(String, Vec<Diagnostic>), String> {
        let Some(program) = &self.program else {
            return Ok(sal_semfront::compile_en(input));
        };
        let mut child = Command::new(program)
            .args(&self.arguments)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|error| format!("cannot start Anglish model command '{program}': {error}"))?;
        let mut stdin = child.stdin.take().expect("requested piped model stdin");
        // Drain output concurrently: a runner writing before EOF must not deadlock
        // against a large input blocked in the other direction.
        let (output, written) = std::thread::scope(|scope| {
            let writer = scope.spawn(move || {
                stdin.write_all(PROMPT.as_bytes())?;
                stdin.write_all(input.as_bytes())
            });
            let output = child.wait_with_output();
            (output, writer.join())
        });
        let output = output.map_err(|error| format!("cannot collect model output: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "Anglish model command failed ({}): {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        written
            .map_err(|_| "Anglish model input writer panicked".to_owned())?
            .map_err(|error| format!("cannot send complete Anglish model input: {error}"))?;
        let source = String::from_utf8(output.stdout)
            .map_err(|error| format!("Anglish model output is not UTF-8: {error}"))?;
        Ok((source, Vec::new()))
    }
}
