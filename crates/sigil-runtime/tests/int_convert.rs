//! PR-A: integer width conversions (`.as_i32()`/`.as_u32()`/`.as_i64()`/
//! `.as_u64()`) + the unsigned-arithmetic codegen fix (U64/U32 div + U64
//! compares). Each tool compiles + runs and decodes a 1 (correct) / 2 (wrong)
//! branch via the negative-sentinel trap (the `array_repeat.rs` idiom). Int
//! conversions are pure (no Alloc), so the tool declares no effect clause.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// Run a body that ends in `if <ok> { return 0 - 1; } else { return 0 - 2; }`
/// and recover 1 (ok) or 2 (wrong) from the negative-sentinel trap.
fn check(body: &str) -> i64 {
    let src = format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n{body}\n}}\n"
    );
    let result = compile_tool(&src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

// ── widening ──

#[test]
fn as_i64_sign_extends_negative_i32() {
    // i32 → i64 must SIGN-extend: (-5):i32 → -5:i64.
    assert_eq!(
        check(
            "    let n: i32 = 0 - 5;\n    let y: i64 = n.as_i64();\n    let e: i64 = 0 - 5;\n    if y == e { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn as_i64_zero_extends_u32() {
    // u32 → i64 must ZERO-extend: a high-bit-set u32 (0xFFFFFFFF) widens to the
    // POSITIVE 4294967295, not -1.
    assert_eq!(
        check(
            "    let neg1: i64 = 0 - 1;\n    let u: u32 = neg1.as_u32();\n    let y: i64 = u.as_i64();\n    let e: i64 = 4294967295;\n    if y == e { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

// ── narrowing (wrapping) ──

#[test]
fn as_u32_wraps_minus_one_to_max() {
    // i64 (-1) → u32 truncates the low 32 bits → 0xFFFFFFFF = 4294967295.
    assert_eq!(
        check(
            "    let n: i64 = 0 - 1;\n    let u: u32 = n.as_u32();\n    let back: i64 = u.as_i64();\n    let e: i64 = 4294967295;\n    if back == e { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn as_u32_truncates_high_bits() {
    // (2^32 + 7) → u32 = 7 (low 32 bits only).
    assert_eq!(
        check(
            "    let n: i64 = 4294967296 + 7;\n    let u: u32 = n.as_u32();\n    let back: i64 = u.as_i64();\n    if back == 7 { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn as_i32_narrows_then_sign_extends_roundtrip() {
    // (-5):i64 → i32 → i64 round-trips through sign-extension.
    assert_eq!(
        check(
            "    let n: i64 = 0 - 5;\n    let y: i32 = n.as_i32();\n    let back: i64 = y.as_i64();\n    let e: i64 = 0 - 5;\n    if back == e { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

// ── reinterpret / identity ──

#[test]
fn as_u64_reinterpret_roundtrip() {
    // i64 ↔ u64 is a bit-preserving reinterpret.
    assert_eq!(
        check(
            "    let n: i64 = 12345;\n    let u: u64 = n.as_u64();\n    let back: i64 = u.as_i64();\n    if back == 12345 { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn as_u32_on_unannotated_int_literal_receiver() {
    // An un-annotated literal `let n = 100;` has type IntLit; `.as_u32()` must
    // still work (IntLit defaults to i64) — consistency with `.contains`.
    assert_eq!(
        check(
            "    let n = 100;\n    let u: u32 = n.as_u32();\n    let back: i64 = u.as_i64();\n    if back == 100 { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

// ── A1: unsigned arithmetic on a u64 ≥ 2^63 (built via .as_u64() on -1/-2) ──

#[test]
fn u64_unsigned_compare_max_gt_five() {
    // u64::MAX (from (-1).as_u64()) > 5 must be TRUE under UNSIGNED compare. A
    // signed compare would treat it as -1 and return false (→ 2).
    assert_eq!(
        check(
            "    let n: i64 = 0 - 1;\n    let big: u64 = n.as_u64();\n    let five: u64 = 5;\n    if big > five { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn u64_unsigned_div_high_value() {
    // (u64::MAX - 1) = 0xFFFF_FFFF_FFFF_FFFE; / 10 (UNSIGNED) =
    // 1844674407370955161 (fits in i64). Signed div would give 0 (→ 2).
    assert_eq!(
        check(
            "    let n: i64 = 0 - 2;\n    let big: u64 = n.as_u64();\n    let ten: u64 = 10;\n    let q: u64 = big / ten;\n    let back: i64 = q.as_i64();\n    let e: i64 = 1844674407370955161;\n    if back == e { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}
