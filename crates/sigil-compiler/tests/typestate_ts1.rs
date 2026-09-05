//! TS1 of the typestate epic — transition checking (T266) + the mint (T269).
//!
//! TS0 gave `File<Open>` the representation + resolution; because the `Named`-arg
//! comparison is INVARIANT, a wrong-state call is already a type error. TS1 (a)
//! mints a stated value from the expected type (`fn open() -> File<Open> { File {…}
//! }`), and (b) routes the wrong-state mismatch to a dedicated **T266** naming the
//! protocol + required + found state. An unpinnable construction is **T269**.

use sigil_compiler::compile_tool;

const MAIN_OPEN_READ: &str = "\
state File { Open, Closed }\n\
record File<@S> { fd: i64 }\n\
fn open() -> File<Open> { return File { fd: 0 }; }\n\
fn read(f: File<Open>) -> i64 { return f.fd; }\n\
fn close(f: File<Open>) -> File<Closed> { return File { fd: 1 }; }\n";

fn codes_of_err(src: &str) -> Vec<String> {
    let err = compile_tool(src).expect_err("expected the program to be rejected");
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_string())
        .collect()
}

// ── the mint: a stated value is born from the expected type ─────────────────────

#[test]
fn mint_via_return_ascription_compiles() {
    // `fn open() -> File<Open> { return File { fd: 0 }; }` — the phantom `@S` is
    // pinned to `Open` by the return type. The legal sequence type-checks.
    let src = format!(
        "module tool;\n{MAIN_OPEN_READ}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let a: File<Open> = open();\n\
         \x20   let n: i64 = read(a);\n\
         \x20   return n;\n\
         }}\n"
    );
    assert!(
        compile_tool(&src).is_ok(),
        "the legal protocol sequence must compile: {:?}",
        compile_tool(&src).err().map(|e| e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect::<Vec<_>>())
    );
}

// ── transition checking: a wrong-state call is T266 ────────────────────────────

#[test]
fn wrong_state_call_rejected_t266() {
    // `read` requires `File<Open>`, but `b` is `File<Closed>` (the result of
    // `close`). The call must be rejected — and with the state-aware T266.
    let src = format!(
        "module tool;\n{MAIN_OPEN_READ}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let a: File<Open> = open();\n\
         \x20   let b: File<Closed> = close(a);\n\
         \x20   let m: i64 = read(b);\n\
         \x20   return m;\n\
         }}\n"
    );
    let cs = codes_of_err(&src);
    assert!(
        cs.iter().any(|c| c == "T266"),
        "a wrong-state call must be T266; got {cs:?}"
    );
}

// ── the unpinnable mint is T269 ────────────────────────────────────────────────

#[test]
fn unpinnable_state_construction_rejected_t269() {
    // `let f = File { fd: 0 };` with no expected type — the phantom `@S` cannot be
    // pinned, so the state is unconstrained: T269 (never defaulted to a state).
    let src = format!(
        "module tool;\n{MAIN_OPEN_READ}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let f = File {{ fd: 0 }};\n\
         \x20   return 0;\n\
         }}\n"
    );
    let cs = codes_of_err(&src);
    assert!(
        cs.iter().any(|c| c == "T269"),
        "an unpinnable typestate construction must be T269; got {cs:?}"
    );
}
