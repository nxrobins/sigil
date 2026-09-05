//! Narrow-int (`i32`/`u32`) RETURN-position range handling.
//!
//! Regression coverage for the return-position sibling of the narrow-int
//! scalar let/assign/call-arg bug (see `narrow_int_literal.rs`). A function
//! with a narrow-int return type that returns an integer literal —
//! `fn f() -> i32 { return 5; }`, even a SINGLE literal — emitted INVALID
//! wasm: the return value's IntLit leaves were never resolved to the
//! function return type, defaulted to i64 at the end-of-typecheck mop-up,
//! and AIR then returned an i64 local from a wasm function whose signature
//! says i32 — a width mismatch that only fails at instantiation.
//!
//! `check_return` now resolves the returned expression's IntLit leaves to
//! the return type (mirroring `check_let`): in range → narrows (valid
//! codegen), out of range → a clean T049 (the return mismatch code).
//!
//! Invariant every case enforces: a narrow-int return is EITHER a clean
//! diagnostic OR compiles + runs, but NEVER a wasm-validation failure.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// A module with a helper fn `f` (the narrow-int return under test) called
/// from `tool_main`, which runs `main_body`.
fn module(helper: &str, main_body: &str) -> String {
    format!(
        "module tool;\n{helper}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{main_body}\n}}\n"
    )
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    /// Type-check rejected it (a clean compile error). Carries the codes.
    Diagnostic(Vec<String>),
    /// The module validated + instantiated (it ran).
    ValidWasm,
    /// `Module::new` rejected the bytes — the bug. Carries the message.
    InvalidWasm(String),
}

fn outcome(src: &str) -> Outcome {
    let compiled = match compile_tool(src) {
        Ok(c) => c,
        Err(e) => {
            return Outcome::Diagnostic(
                e.diagnostics()
                    .iter()
                    .map(|d| d.code().as_str().to_string())
                    .collect(),
            );
        }
    };
    match execute_ephemeral(&compiled.wasm, b"", compiled.fuel_budget, &IoGrants::none()) {
        Ok(_) => Outcome::ValidWasm,
        // `Module::new` failure surfaces as a Trapped with wasmtime's
        // "failed to compile: wasm[..]" prefix — the invalid-wasm signature.
        // Any OTHER trap (incl. the `return 0 - n` sentinel) means the
        // module instantiated fine, i.e. it WAS valid wasm.
        Err(ToolError::Trapped { message }) if message.contains("failed to compile") => {
            Outcome::InvalidWasm(message)
        }
        Err(_) => Outcome::ValidWasm,
    }
}

/// Decode the negative-sentinel return convention (`return 0 - value;` →
/// the runtime reports `Trapped` with a POSITIVE `value`).
fn neg(src: &str) -> i64 {
    let result = compile_tool(src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected a sentinel"),
    }
}

// ── The core invariant: never invalid wasm ───────────────────────────────────

#[test]
fn narrow_int_returns_never_emit_invalid_wasm() {
    // (label, helper fn, main body, expected outcome). main body just calls
    // f into a same-typed local and returns a sentinel; the diagnostic cases
    // fail to compile in `f` itself regardless.
    let cases: Vec<(&str, &str, &str, Outcome)> = vec![
        // ---- i32 ----
        (
            "ret i32 = 5 (single literal)",
            "fn f() -> i32 { return 5; }",
            "let v: i32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret i32 = 0 - 5 (in-range binary)",
            "fn f() -> i32 { return 0 - 5; }",
            "let v: i32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret i32 = 2147483647 (i32::MAX)",
            "fn f() -> i32 { return 2147483647; }",
            "let v: i32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret i32 = 0 - 2147483647 - 1 (i32::MIN, in-range leaves)",
            "fn f() -> i32 { return 0 - 2147483647 - 1; }",
            "let v: i32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret i32 = 2147483648 (single literal, out of range)",
            "fn f() -> i32 { return 2147483648; }",
            "let v: i32 = f();\nreturn 0 - 1;",
            Outcome::Diagnostic(vec!["T049".into()]),
        ),
        (
            "ret i32 = 0 - 2147483648 (overflowing leaf in a binary)",
            "fn f() -> i32 { return 0 - 2147483648; }",
            "let v: i32 = f();\nreturn 0 - 1;",
            Outcome::Diagnostic(vec!["T049".into()]),
        ),
        // ---- u32 ----
        (
            "ret u32 = 5 (single literal)",
            "fn f() -> u32 { return 5; }",
            "let v: u32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret u32 = 2147483648 (2^31 fits u32)",
            "fn f() -> u32 { return 2147483648; }",
            "let v: u32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret u32 = 4294967295 (u32::MAX)",
            "fn f() -> u32 { return 4294967295; }",
            "let v: u32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret u32 = 1 + 2 (in-range binary)",
            "fn f() -> u32 { return 1 + 2; }",
            "let v: u32 = f();\nreturn 0 - 1;",
            Outcome::ValidWasm,
        ),
        (
            "ret u32 = 4294967296 (single literal, out of range)",
            "fn f() -> u32 { return 4294967296; }",
            "let v: u32 = f();\nreturn 0 - 1;",
            Outcome::Diagnostic(vec!["T049".into()]),
        ),
    ];

    for (label, helper, main_body, expected) in &cases {
        let src = module(helper, main_body);
        let got = outcome(&src);
        assert!(
            !matches!(got, Outcome::InvalidWasm(_)),
            "INVALID WASM for case `{label}`: {got:?}\n--- source ---\n{src}"
        );
        assert_eq!(&got, expected, "unexpected outcome for case `{label}`");
    }
}

// ── Out-of-range returns are a clean T049 ─────────────────────────────────────

#[test]
fn out_of_range_return_is_t049() {
    for helper in [
        "fn f() -> i32 { return 2147483648; }",
        "fn f() -> i32 { return 0 - 2147483648; }",
        "fn f() -> u32 { return 4294967296; }",
        "fn f() -> u32 { return 0 - 4294967296; }",
    ] {
        let src = module(helper, "let v: i32 = 0;\nreturn 0 - 1;");
        assert_eq!(
            outcome(&src),
            Outcome::Diagnostic(vec!["T049".into()]),
            "expected a clean T049 for `{helper}`",
        );
    }
}

// ── In-range narrow-int returns compute the right value ───────────────────────

#[test]
fn i32_single_literal_return_value() {
    let src = module(
        "fn f() -> i32 { return 5; }",
        "let v: i32 = f();\nif v == 5 { return 0 - 111; } else { return 0 - 222; }",
    );
    assert_eq!(neg(&src), 111, "f() should return 5");
}

#[test]
fn i32_binary_return_value() {
    let src = module(
        "fn f() -> i32 { return 0 - 5; }",
        "let v: i32 = f();\nlet z: i32 = v + 5;\nif z == 0 { return 0 - 111; } else { return 0 - 222; }",
    );
    assert_eq!(neg(&src), 111, "f() should return -5");
}

#[test]
fn i32_min_and_max_return_round_trip() {
    // f returns i32::MIN via the in-range idiom; g returns i32::MAX. Their
    // sum is -1 (no i32 overflow), exercising both boundary return values.
    let src = module(
        "fn lo() -> i32 { return 0 - 2147483647 - 1; }\nfn hi() -> i32 { return 2147483647; }",
        "let s: i32 = lo() + hi();\nif s == 0 - 1 { return 0 - 111; } else { return 0 - 222; }",
    );
    assert_eq!(neg(&src), 111, "i32::MIN + i32::MAX should be -1");
}

#[test]
fn u32_max_return_round_trips() {
    let src = module(
        "fn f() -> u32 { return 4294967295; }",
        "let v: u32 = f();\nif v == 4294967295 { return 0 - 111; } else { return 0 - 222; }",
    );
    assert_eq!(neg(&src), 111, "f() should return u32::MAX");
}
