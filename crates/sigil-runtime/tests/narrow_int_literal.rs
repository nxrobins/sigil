//! Narrow-int (`i32`/`u32`) constant-initializer range handling.
//!
//! Regression coverage for the bug where a narrow-int `let`/assignment/
//! call-argument whose initializer was a binary expression with an
//! out-of-range integer-literal LEAF (e.g. `let n: i32 = 0 - 2147483648`,
//! the `0 - 2^31` idiom for `i32::MIN`) emitted INVALID wasm: the leaf
//! overflowed i32, stayed `Type::IntLit`, was defaulted to i64 by the
//! end-of-typecheck mop-up, and AIR then fed an i64 operand to an
//! `i32.sub` — a module that only failed at instantiation.
//!
//! The type-checker now rejects an out-of-range literal leaf with the
//! calling site's own mismatch code (T041 let / T045 assign / T071
//! argument), exactly like the single-literal `let n: i32 = 2147483648`
//! overflow. Crucially the reassignment path also now resolves IntLit
//! leaves to the place type at all, so an IN-RANGE binary RHS like
//! `n = 0 - 5` — previously also invalid wasm — compiles and runs.
//!
//! The load-bearing invariant every case below enforces: a narrow-int
//! constant initializer is EITHER a clean diagnostic OR compiles + runs,
//! but NEVER a wasm-validation failure.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// tool_main-only module.
fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

/// Module with extra top-level items (helper fns) before tool_main.
fn tool_with(items: &str, body: &str) -> String {
    format!(
        "module tool;\n{items}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    )
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    /// Type-check rejected it (a clean compile error). Carries the codes.
    Diagnostic(Vec<String>),
    /// The module validated + instantiated (it ran; it may then have
    /// returned the negative-sentinel convention, which is still a
    /// perfectly valid module).
    ValidWasm,
    /// `Module::new` rejected the bytes — the bug. Carries the message.
    InvalidWasm(String),
}

/// Classify a whole-module source by the load-bearing distinction:
/// clean diagnostic vs valid-and-ran vs invalid-wasm.
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
        // "failed to compile: wasm[..]" prefix — that is the invalid-wasm
        // signature. Any OTHER trap (incl. the `return 0 - n` sentinel)
        // means the module instantiated fine, i.e. it WAS valid wasm.
        Err(ToolError::Trapped { message }) if message.contains("failed to compile") => {
            Outcome::InvalidWasm(message)
        }
        Err(_) => Outcome::ValidWasm,
    }
}

/// Decode the negative-sentinel return convention (`return 0 - value;` →
/// the runtime reports `Trapped` with a POSITIVE `value`). Asserts the
/// module compiled and ran.
fn neg(body: &str) -> i64 {
    let src = tool(body);
    let result = compile_tool(&src).expect("tool should compile");
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

/// Every narrow-int constant-initializer case — across let, reassignment,
/// and call-argument positions, in range and out of range — must resolve
/// to EITHER a clean diagnostic OR a valid module. None may produce
/// invalid wasm. This single matrix is the direct regression guard.
#[test]
fn narrow_int_initializers_never_emit_invalid_wasm() {
    // (label, full module source, expected outcome)
    let cases: Vec<(&str, String, Outcome)> = vec![
        // ---- let, i32 ----
        (
            "let i32 = 0 - 2147483648 (i32::MIN via overflowing leaf)",
            tool("let n: i32 = 0 - 2147483648;\nreturn 0 - 1;"),
            Outcome::Diagnostic(vec!["T041".into()]),
        ),
        (
            "let i32 = 2147483647 (i32::MAX, single literal)",
            tool("let n: i32 = 2147483647;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        (
            "let i32 = 0 - 2147483647 - 1 (i32::MIN, all leaves in range)",
            tool("let n: i32 = 0 - 2147483647 - 1;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        (
            "let i32 = 2147483648 (single literal, just out of range)",
            tool("let n: i32 = 2147483648;\nreturn 0 - 1;"),
            Outcome::Diagnostic(vec!["T041".into()]),
        ),
        (
            "let i32 = 0 - 5 (in-range subtraction)",
            tool("let n: i32 = 0 - 5;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        // ---- let, u32 ----
        (
            "let u32 = 2147483648 (2^31 fits u32)",
            tool("let n: u32 = 2147483648;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        (
            "let u32 = 4294967295 (u32::MAX, single literal)",
            tool("let n: u32 = 4294967295;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        (
            "let u32 = 4294967296 (single literal, just out of range)",
            tool("let n: u32 = 4294967296;\nreturn 0 - 1;"),
            Outcome::Diagnostic(vec!["T041".into()]),
        ),
        (
            "let u32 = 0 - 4294967296 (overflowing leaf in a binary)",
            tool("let n: u32 = 0 - 4294967296;\nreturn 0 - 1;"),
            Outcome::Diagnostic(vec!["T041".into()]),
        ),
        (
            "let u32 = 1 + 2 (in-range addition)",
            tool("let n: u32 = 1 + 2;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        // ---- reassignment ----
        (
            "assign i32 n = 0 - 2147483648 (overflowing leaf)",
            tool("let mut n: i32 = 0;\nn = 0 - 2147483648;\nreturn 0 - 1;"),
            Outcome::Diagnostic(vec!["T045".into()]),
        ),
        (
            "assign i32 n = 0 - 5 (in-range binary RHS — was invalid wasm)",
            tool("let mut n: i32 = 0;\nn = 0 - 5;\nreturn 0 - 1;"),
            Outcome::ValidWasm,
        ),
        (
            "assign i32 n = 2147483648 (single literal, out of range)",
            tool("let mut n: i32 = 0;\nn = 2147483648;\nreturn 0 - 1;"),
            Outcome::Diagnostic(vec!["T045".into()]),
        ),
        // ---- call argument ----
        (
            "call takes_i32(0 - 2147483648) (overflowing leaf in arg)",
            tool_with(
                "fn takes_i32(x: i32) -> i64 { return 0 - 1; }",
                "return takes_i32(0 - 2147483648);",
            ),
            Outcome::Diagnostic(vec!["T071".into()]),
        ),
        (
            "call takes_i32(0 - 5) (in-range arg)",
            tool_with(
                "fn takes_i32(x: i32) -> i64 { return 0 - 1; }",
                "return takes_i32(0 - 5);",
            ),
            Outcome::ValidWasm,
        ),
    ];

    for (label, src, expected) in &cases {
        let got = outcome(src);
        // The non-negotiable invariant, called out explicitly for a clear
        // failure message if it ever regresses.
        assert!(
            !matches!(got, Outcome::InvalidWasm(_)),
            "INVALID WASM for case `{label}`: {got:?}\n--- source ---\n{src}"
        );
        assert_eq!(&got, expected, "unexpected outcome for case `{label}`");
    }
}

// ── Out-of-range literals are clean diagnostics at every site ─────────────────

#[test]
fn out_of_range_leaf_reports_the_site_mismatch_code() {
    // let -> T041
    assert_eq!(
        outcome(&tool("let n: i32 = 0 - 2147483648;\nreturn 0 - 1;")),
        Outcome::Diagnostic(vec!["T041".into()]),
    );
    // assignment -> T045
    assert_eq!(
        outcome(&tool(
            "let mut n: i32 = 0;\nn = 0 - 2147483648;\nreturn 0 - 1;"
        )),
        Outcome::Diagnostic(vec!["T045".into()]),
    );
    // call argument -> T071
    assert_eq!(
        outcome(&tool_with(
            "fn takes_i32(x: i32) -> i64 { return 0 - 1; }",
            "return takes_i32(0 - 2147483648);",
        )),
        Outcome::Diagnostic(vec!["T071".into()]),
    );
}

// ── In-range narrow-int values are computed correctly ─────────────────────────

#[test]
fn i32_min_and_max_round_trip() {
    // i32::MIN (0 - 2147483647 - 1) + i32::MAX (2147483647) == -1, with no
    // i32 overflow at any step. Verifying the sum exercises both boundary
    // values through let-binding + i32 arithmetic + comparison.
    let body = "let lo: i32 = 0 - 2147483647 - 1;\n\
                let hi: i32 = 2147483647;\n\
                let s: i32 = lo + hi;\n\
                if s == 0 - 1 { return 0 - 111; } else { return 0 - 222; }";
    assert_eq!(neg(body), 111, "i32::MIN + i32::MAX should be -1");
}

#[test]
fn u32_max_round_trips() {
    // u32::MAX two ways: the direct literal and an in-range `+ 1`. They
    // must compare equal (same 0xFFFF_FFFF bit pattern).
    let body = "let direct: u32 = 4294967295;\n\
                let built: u32 = 4294967294 + 1;\n\
                if direct == built { return 0 - 111; } else { return 0 - 222; }";
    assert_eq!(neg(body), 111, "u32::MAX should round-trip");
}

#[test]
fn in_range_subtraction_has_the_right_value() {
    // n == -5; n + 5 == 0.
    let body = "let n: i32 = 0 - 5;\n\
                let z: i32 = n + 5;\n\
                if z == 0 { return 0 - 111; } else { return 0 - 222; }";
    assert_eq!(neg(body), 111, "0 - 5 should be -5");
}

#[test]
fn in_range_binary_reassignment_runs_and_is_correct() {
    // The reassignment path historically never resolved IntLit leaves, so
    // even this in-range `n = 0 - 5` produced invalid wasm. Confirm it now
    // both validates AND stores the right value.
    let body = "let mut n: i32 = 0;\n\
                n = 0 - 5;\n\
                let z: i32 = n + 5;\n\
                if z == 0 { return 0 - 111; } else { return 0 - 222; }";
    assert_eq!(neg(body), 111, "reassigned `n = 0 - 5` should be -5");
}
