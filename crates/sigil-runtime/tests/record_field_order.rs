//! Record constructs with fields written OUT of decl order must still store
//! every field at its DECL offset — the runtime round-trip.
//!
//! The miscompile this pins (caught by SH-AIR-CV-5's Phase-0 probe):
//! `air::lower` kept `RecordConstruct.fields` in WRITTEN order and
//! `memory::flatten_record` assigns offsets by accumulating widths in vec
//! order, while field READS use the registry's decl-order offsets
//! (`field_base_and_offset`). So `R { y: b, x: a }` stored `x` at `y`'s
//! offset and every read returned silently wrong values. The fix normalizes
//! the construct's field vec to decl order at lowering (evaluation of the
//! field value expressions stays in written order — the mats are emitted
//! before the sort).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Wrap `body` in a tool module carrying record `decls` (constructs allocate).
fn rec_tool(decls: &str, body: &str) -> String {
    format!(
        "module tool;\n{decls}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// Run a `return 0 - value;` body and recover `value` from the
/// negative-sentinel trap (the `array_contains.rs` pattern).
fn neg(decls: &str, body: &str) -> i64 {
    let result = compile_tool(&rec_tool(decls, body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected negative sentinel"),
    }
}

/// Same-width swap: `P { b: 2, a: 41 }` — under the bug `a` reads back `b`'s
/// value (2); correct is 41.
#[test]
fn swapped_same_width_reads_decl_field() {
    let v = neg(
        "record P { a: i64, b: i64 }",
        "    let p: P = P { b: 2, a: 41 };\n    return 0 - p.a;",
    );
    assert_eq!(v, 41, "p.a must read the value written for `a`");
}

/// Mixed-width swap: `R {{ y: 7, x: 258 }}` — under the bug `x` (decl offset 0,
/// I64) reads bytes that hold `y`'s U32 plus `x`'s low half.
#[test]
fn swapped_mixed_width_reads_decl_field() {
    let v = neg(
        "record R { x: i64, y: u32 }",
        "    let r: R = R { y: 7, x: 258 };\n    return 0 - r.x;",
    );
    assert_eq!(v, 258, "r.x must read the value written for `x`");
}

/// Control: a decl-order construct is unchanged by the normalization.
#[test]
fn decl_order_construct_unchanged() {
    let v = neg(
        "record R { x: i64, y: u32 }",
        "    let r: R = R { x: 258, y: 7 };\n    return 0 - r.x;",
    );
    assert_eq!(v, 258, "the in-order path must be unaffected");
}

/// Evaluation order stays WRITTEN order: field value expressions are calls
/// whose side effects (fuel debits aside) we can't observe directly, so pin
/// the observable proxy — a swapped construct built from call results still
/// reads back per-field correct values.
#[test]
fn swapped_call_valued_fields() {
    let v = neg(
        "record Q { a: i64, b: i64 }\nfn mk(n: i64) -> i64 { return n + 1; }",
        "    let q: Q = Q { b: mk(1), a: mk(40) };\n    return 0 - q.a;",
    );
    assert_eq!(v, 41, "q.a must hold mk(40) == 41");
}
