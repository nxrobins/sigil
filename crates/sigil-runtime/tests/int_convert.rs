//! PR-A: integer width conversions (`.as_i32()`/`.as_u32()`/`.as_i64()`/
//! `.as_u64()`) + the unsigned-arithmetic codegen fix (U64/U32 div + U64
//! compares) + the widening a 4-byte `ct_*` operand needs before the
//! constant-time intrinsics take it, `ct_lt`'s order on every 8-byte pair,
//! at the extremes where the difference overflows, and the literal-binding gap
//! (an un-annotated literal binding's `i64` local), pinned as it stands beside
//! a `u64` and rejected where a use checks it as an `i32`. Each tool compiles +
//! runs and decodes a 1 (correct) / 2 (wrong) branch via the negative-sentinel
//! trap (the `array_repeat.rs` idiom); the `ct_lt` pair matrices return 3 + the
//! index of the first wrong pair instead of 2. Int conversions and the `ct_*`
//! intrinsics are pure (no Alloc), so the tool declares no effect clause.

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

// ── widening a 4-byte ct_* operand, the remedy the type checker names ──
//
// `ct_eq`, `ct_lt` and `ct_select` take 8-byte operands only. The T075 a 4-byte operand draws
// says `.as_i64()` and `.as_u64()` both sign-extend an `i32` and zero-extend a `u32` (the
// IntConvert lowering picks the extension from the SOURCE width, not the target), and that
// `ct_lt` keeps an `i32`'s order only through `.as_i64()`. Run here at the 4-byte boundaries: a
// negative `i32`, `i32::MIN` against `i32::MAX`, and `u32` values of 2^31 or more, which a
// sign-extension would turn negative. A `u32` keeps its order through either conversion, and an
// `i32` through `.as_i64()`. Through `.as_u64()` an `i32` becomes a `u64`, which `ct_lt` compares
// unsigned, so a negative one orders above every non-negative one:
// `ct_lt_orders_an_i32_widened_to_u64_by_its_unsigned_bits` pins that order, the hint's warning.

#[test]
fn ct_lt_orders_widened_i32_operands_by_signed_value() {
    assert_eq!(
        check(
            "    let a: i32 = 0 - 1;\n    let b: i32 = 1;\n    let lo: i32 = 0 - 2147483647 - 1;\n    let hi: i32 = 2147483647;\n    let ab: bool = ct_lt(a.as_i64(), b.as_i64());\n    let ba: bool = ct_lt(b.as_i64(), a.as_i64());\n    let lohi: bool = ct_lt(lo.as_i64(), hi.as_i64());\n    let hilo: bool = ct_lt(hi.as_i64(), lo.as_i64());\n    if ab && lohi && !ba && !hilo { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn ct_lt_orders_widened_u32_operands_by_unsigned_value() {
    // Sign-extended, 2^31 and u32::MAX would be negative and order below 1 and 0.
    assert_eq!(
        check(
            "    let top: u32 = 2147483648;\n    let one: u32 = 1;\n    let max: u32 = 4294967295;\n    let zero: u32 = 0;\n    let top_one: bool = ct_lt(top.as_i64(), one.as_i64());\n    let one_top: bool = ct_lt(one.as_i64(), top.as_i64());\n    let max_zero: bool = ct_lt(max.as_u64(), zero.as_u64());\n    let zero_max: bool = ct_lt(zero.as_u64(), max.as_u64());\n    if one_top && zero_max && !top_one && !max_zero { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn ct_lt_orders_an_i32_widened_to_u64_by_its_unsigned_bits() {
    // `.as_u64()` sign-extends -1 into u64::MAX, which `ct_lt` (unsigned for two `u64`) orders
    // above 1; two negatives keep their order, since i32::MIN's bits are below -1's. Before the
    // `ct_lt` overflow fix this pair compared signed and read -1 below 1, so this fails there.
    assert_eq!(
        check(
            "    let a: i32 = 0 - 1;\n    let b: i32 = 1;\n    let lo: i32 = 0 - 2147483647 - 1;\n    let ab: bool = ct_lt(a.as_u64(), b.as_u64());\n    let ba: bool = ct_lt(b.as_u64(), a.as_u64());\n    let lo_a: bool = ct_lt(lo.as_u64(), a.as_u64());\n    let a_lo: bool = ct_lt(a.as_u64(), lo.as_u64());\n    if !ab && ba && lo_a && !a_lo { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn ct_eq_and_ct_select_see_the_widened_value() {
    // `.as_u64()` sign-extends a negative `i32` (the bits of -5 as an i64), `.as_i64()`
    // zero-extends a `u32` (u32::MAX stays 4294967295, not -1), and `ct_select` hands either
    // widened value through unchanged.
    assert_eq!(
        check(
            "    let n: i32 = 0 - 5;\n    let m: u32 = 4294967295;\n    let n64: i64 = 0 - 5;\n    let n_bits: u64 = n64.as_u64();\n    let m64: i64 = 4294967295;\n    let minus_one: i64 = 0 - 1;\n    let sign_extended: bool = ct_eq(n.as_u64(), n_bits);\n    let zero_extended: bool = ct_eq(m.as_i64(), m64);\n    let negative: bool = ct_eq(m.as_i64(), minus_one);\n    let t: i64 = ct_select(true, n.as_i64(), m.as_i64());\n    let f: i64 = ct_select(false, n.as_i64(), m.as_i64());\n    if sign_extended && zero_extended && !negative && (t == n64) && (f == m64) { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

// ── ct_lt on every 8-byte pair, at the extremes where the difference overflows ──
//
// `ct_lt` once returned the sign bit of the wrapping `a - b`: `i64::MIN < 1` read false,
// `i64::MAX < -1` read true, and a `u64` of 2^63 or more read as negative (the CLOSED entry in
// tests/attack/KNOWN_GAPS.md). It now takes the sign bit of an overflow-safe word, signed for two
// `i64` and unsigned for two `u64`. Each matrix below runs `ct_lt` on EVERY ordered pair of a set
// that holds both ends of the type and the values on each side of its sign boundary, against
// Rust's own `<` on the same values; a wrong pair comes back by index, so a failure names it. Run
// against the lowering before the fix, both matrices fail.

/// A SIGIL `i64` expression for `v`: a negative value as a subtraction, and `i64::MIN` as two,
/// since its magnitude has no `i64` literal (a literal past `i64::MAX` is a `u256`).
fn i64_expr(v: i64) -> String {
    match v {
        i64::MIN => "0 - 9223372036854775807 - 1".to_string(),
        v if v < 0 => format!("0 - {}", -v),
        v => v.to_string(),
    }
}

/// Run `ct_lt(v{i}, v{j})` for every ordered pair of `values`, where `bind(i, v)` declares the
/// local `v{i}` holding `v`, and return the first pair whose answer is not Rust's `a < b`, or
/// `None` when every answer is.
fn ct_lt_first_wrong_pair<T: Copy + Ord>(
    values: &[T],
    bind: impl Fn(usize, T) -> String,
) -> Option<(T, T)> {
    let mut body = String::new();
    for (i, v) in values.iter().enumerate() {
        body.push_str(&bind(i, *v));
    }
    let mut pairs = Vec::new();
    for (i, a) in values.iter().enumerate() {
        for (j, b) in values.iter().enumerate() {
            let k = pairs.len();
            let wrong_if = if a < b { "!" } else { "" };
            body.push_str(&format!(
                "    let p{k}: bool = ct_lt(v{i}, v{j});\n    if {wrong_if}p{k} {{ return 0 - {}; }}\n",
                k + 3
            ));
            pairs.push((*a, *b));
        }
    }
    body.push_str("    return 0 - 1;");
    match check(&body) {
        1 => None,
        n => {
            let index = usize::try_from(n - 3).expect("a wrong pair comes back as 3 + its index");
            Some(*pairs.get(index).expect("the index names a pair"))
        }
    }
}

#[test]
fn ct_lt_orders_every_i64_pair_at_the_extremes() {
    let values = [
        i64::MIN,
        i64::MIN + 1,
        -(1 << 62),
        -1,
        0,
        1,
        1 << 62,
        i64::MAX - 1,
        i64::MAX,
    ];
    let first_wrong = ct_lt_first_wrong_pair(&values, |i, v| {
        format!("    let v{i}: i64 = {};\n", i64_expr(v))
    });
    assert_eq!(
        first_wrong, None,
        "ct_lt must give the signed order of two i64"
    );
}

#[test]
fn ct_lt_orders_every_u64_pair_at_the_extremes() {
    let values = [
        0,
        1,
        1 << 62,
        (1 << 63) - 1,
        1 << 63,
        (1 << 63) + 1,
        u64::MAX - 1,
        u64::MAX,
    ];
    // A `u64` past i64::MAX has no literal: build its bits as an `i64` and reinterpret them.
    let first_wrong = ct_lt_first_wrong_pair(&values, |i, v| match i64::try_from(v) {
        Ok(small) => format!("    let v{i}: u64 = {small};\n"),
        Err(_) => format!(
            "    let w{i}: i64 = {};\n    let v{i}: u64 = w{i}.as_u64();\n",
            i64_expr(v as i64)
        ),
    });
    assert_eq!(
        first_wrong, None,
        "ct_lt must give the unsigned order of two u64"
    );
}

#[test]
fn ct_lt_orders_a_literal_beside_a_u64_by_unsigned_value() {
    // An integer literal beside a `u64` checks as a `u64`, so the pair compares unsigned. That
    // holds for an un-annotated literal binding too, whose local stays an `i64`: the AIR statement
    // carries the order, not the operand locals. Read as signed, u64::MAX is -1 and orders below 5.
    assert_eq!(
        check(
            "    let five = 5;\n    let minus_one: i64 = 0 - 1;\n    let max: u64 = minus_one.as_u64();\n    let bound_max: bool = ct_lt(five, max);\n    let max_bound: bool = ct_lt(max, five);\n    let literal_max: bool = ct_lt(5, max);\n    let max_literal: bool = ct_lt(max, 5);\n    if bound_max && literal_max && !max_bound && !max_literal { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

// ── known gap: an un-annotated literal binding keeps an i64 local where it checks as another type ──
//
// `let n = 5;` (or `let (a, b) = (5, 6);`) checks as the type each use gives it (an integer
// literal beside a `u64` is a `u64`), but the binding's local keeps the default `i64`, and the
// emitter takes a binary operator's signedness and width from its left operand's local. Beside a
// `u64` it is pinned AS IT STANDS (tests/attack/KNOWN_GAPS.md, OPEN), by a test written to FAIL
// when the gap is closed for any of its shapes: then pin the checked type's answer here and close
// the entry. Where a use checks it as an `i32`, the type checker now rejects it (SR-032).

#[test]
fn known_gap_literal_binding_beside_a_u64_takes_signed_arithmetic() {
    // Beside u64::MAX, which an `i64` local reads as -1, `<`, `<=`, `>`, `>=`, `/`, `%` and `>>`
    // each give the signed answer, and so does `<` on a binding a tuple pattern makes. The controls
    // give the unsigned one: the literal itself, an annotated `u64` binding, and `ct_lt`, whose
    // order AIR carries from the checked types.
    assert_eq!(
        check(
            "    let five = 5;\n    let ten = 10;\n    let all_ones = 0 - 1;\n    let (six, seven) = (6, 7);\n    let five_u: u64 = 5;\n    let minus_one: i64 = 0 - 1;\n    let max: u64 = minus_one.as_u64();\n    let one: u64 = 1;\n    let top_clear: u64 = 9223372036854775807;\n    let lt: bool = five < max;\n    let le: bool = five <= max;\n    let gt: bool = five > max;\n    let ge: bool = five >= max;\n    let q: u64 = ten / max;\n    let r: u64 = ten % max;\n    let s: u64 = all_ones >> one;\n    let tuple_lt: bool = six < max;\n    let signed: bool = !lt && !le && gt && ge && (q != 0) && (r == 0) && (s != top_clear) && !tuple_lt;\n    let controls: bool = (5 < max) && (five_u < max) && ct_lt(five, max);\n    if signed && controls { return 0 - 1; } else { return 0 - 2; }"
        ),
        1
    );
}

#[test]
fn literal_binding_used_as_an_i32_is_rejected_at_the_use() {
    // Where a use checks it as an `i32` (assigned to one, beside an `i32` operand on either side,
    // passed to an `i32` parameter), the binding's `i64` local met an `i32` one, and the module
    // did not validate: wasmtime refused it, but the checker had accepted the program. The checker
    // now rejects each use with the site's own code, for a `let` binding and a tuple-pattern one
    // (SR-032: a value typed by an integer literal before its slot was known is stored at the
    // `i64` default, which a 4-byte slot does not take). Each annotated twin validates, so each
    // rejection is the binding's.
    for (use_site, code) in [
        ("let k: i32 = n;", "T041"),
        ("let k: i32 = x + n;", "T054"),
        ("let k: i32 = n + x;", "T054"),
        ("let k: bool = x == n;", "T055"),
        ("let k: i64 = f(n);", "T071"),
    ] {
        let tool = |binding: &str| {
            format!(
                "module tool;\nfn f(v: i32) -> i64 {{\n    return v.as_i64();\n}}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    let x: i32 = 3;\n    {binding}\n    {use_site}\n    return input_len;\n}}\n"
            )
        };
        let annotated = compile_tool(&tool("let n: i32 = 5;"))
            .unwrap_or_else(|e| panic!("{use_site}: the annotated twin must compile: {e:?}"));
        wasmparser::validate(&annotated.wasm).unwrap_or_else(|e| {
            panic!("{use_site}: the annotated twin's module must validate: {e}")
        });
        for binding in ["let n = 5;", "let (n, m) = (5, 6);"] {
            let codes: Vec<String> = match compile_tool(&tool(binding)) {
                Ok(_) => Vec::new(),
                Err(e) => e
                    .diagnostics()
                    .iter()
                    .map(|d| d.code().as_str().to_string())
                    .collect(),
            };
            assert_eq!(
                codes,
                [code],
                "{binding} {use_site}: the literal binding must be rejected at the use"
            );
        }
    }
}
