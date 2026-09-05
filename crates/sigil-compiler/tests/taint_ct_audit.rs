//! Phase 2H Phase C — Constant-time codegen byte-scan audit.
//!
//! Compiles a CT-only fixture exercising every CT intrinsic on @SecretCT
//! operands, then walks the emitted Wasm code section with wasmparser
//! and asserts that no forbidden opcodes appear inside any function body.
//!
//! The typecheck pass (Phase A) already rejects every CT-violating source
//! construct before AIR lowering, so a violation reaching the Wasm output
//! would represent a codegen-side regression. This test is the regression
//! guard the spec calls "the only post-typecheck check" (§4.2 item 1).
//!
//! Forbidden opcode set (spec §10.16):
//!   {if, else, br_if, br_table, select, i32.div_*, i32.rem_*,
//!    i64.div_*, i64.rem_*}
//!
//! Note: `i64.shr_s`/`shl`/`shr_u` are NOT forbidden because Sigil's
//! surface language has no variable-shift BinaryOp today (CT008/CT009
//! are spec-reserved). The only shifts present in CT scope are
//! constant-amount shifts (e.g. ct_lt's `>> 63`), which are
//! data-independent on every supported CPU.

use sigil_compiler::compile_named_module;
use wasmparser::{Operator, Parser, Payload};

/// CT-only fixture: every @SecretCT value flows through ct_eq, ct_select,
/// and ct_lt only. If codegen ever introduces `if`, `br_if`, `select`,
/// or division for one of these operations, the byte-scan catches it.
const CT_FIXTURE: &str = r#"module tool;

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    // Bring values into @SecretCT scope via E1-permitted @Public → @SecretCT
    // upcast. Then exercise all three CT intrinsics so the byte-scan
    // inspects their actual emission.
    let a: i64 @SecretCT = 42;
    let b: i64 @SecretCT = 99;
    let eq_result: bool @SecretCT = ct_eq(a, b);
    let chosen: i64 @SecretCT = ct_select(eq_result, a, b);
    let lt_result: bool @SecretCT = ct_lt(a, b);
    return 0;
}
"#;

#[test]
fn ct_intrinsics_emit_no_forbidden_opcodes() {
    let compilation = compile_named_module("ct_audit_fixture.sigil", CT_FIXTURE)
        .expect("CT fixture should compile");

    let wasm = &compilation.wasm_inner;

    // Collect every violation; report all at once for easier debugging.
    let mut violations: Vec<String> = Vec::new();
    let mut fn_index: u32 = 0;

    for payload in Parser::new(0).parse_all(wasm) {
        let payload = payload.expect("wasm payload should parse");
        if let Payload::CodeSectionEntry(body) = payload {
            let mut ops = body
                .get_operators_reader()
                .expect("operator reader should parse");
            while !ops.eof() {
                let op = ops.read().expect("operator should parse");
                if is_forbidden_in_ct_scope(&op) {
                    violations.push(format!("fn #{fn_index}: forbidden opcode `{op:?}`"));
                }
            }
            fn_index += 1;
        }
    }

    assert!(
        violations.is_empty(),
        "CT audit: forbidden opcodes appeared in CT-only fixture output:\n  {}",
        violations.join("\n  ")
    );
    assert!(
        fn_index > 0,
        "audit must scan at least one function body — fixture compiled to {} bytes with no \
         code section entries, which means the test isn't proving anything",
        wasm.len()
    );
}

#[test]
fn ct_audit_detector_sees_division() {
    // Sanity check: if a future codegen change introduces division into
    // a CT function, this test would fail. We can't force a regression
    // from outside the compiler, so this test confirms the detection
    // mechanism works by scanning a deliberately non-CT fixture that
    // DOES use division and asserting we'd see it.
    let div_fixture = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return input_ptr / input_len;
}
"#;
    let compilation = compile_named_module("ct_audit_div.sigil", div_fixture)
        .expect("divides fixture should compile");
    let wasm = &compilation.wasm_inner;

    let mut saw_div = false;
    for payload in Parser::new(0).parse_all(wasm) {
        if let Payload::CodeSectionEntry(body) = payload.expect("wasm payload should parse") {
            let mut ops = body
                .get_operators_reader()
                .expect("operator reader should parse");
            while !ops.eof() {
                let op = ops.read().expect("operator should parse");
                if matches!(
                    op,
                    Operator::I64DivS | Operator::I64DivU | Operator::I32DivS | Operator::I32DivU
                ) {
                    saw_div = true;
                }
            }
        }
    }
    assert!(
        saw_div,
        "audit detector smoke test: division opcode must be detectable in plain `a / b` code"
    );
}

/// Opcodes forbidden inside any function in CT scope. See
/// `docs/specs/secret-ct.md` §10.16 for the canonical list.
fn is_forbidden_in_ct_scope(op: &Operator<'_>) -> bool {
    matches!(
        op,
        // Explicit branching constructs.
        Operator::If { .. }
        | Operator::Else
        | Operator::BrIf { .. }
        | Operator::BrTable { .. }
        // Wasm `select` — some backends compile this to a CPU branch on
        // certain ISAs; ct_select MUST be lowered to a branch-free
        // bitwise chain, never to Wasm select.
        | Operator::Select
        | Operator::TypedSelect { .. }
        // Variable-time division/modulo on either width.
        | Operator::I32DivS
        | Operator::I32DivU
        | Operator::I32RemS
        | Operator::I32RemU
        | Operator::I64DivS
        | Operator::I64DivU
        | Operator::I64RemS
        | Operator::I64RemU
    )
}
