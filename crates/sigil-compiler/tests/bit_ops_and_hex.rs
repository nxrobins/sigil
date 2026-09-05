//! Integration tests for hex integer literals and bit operators.
//!
//! These are axis-1 (expressiveness) additions that ride on PR #32's
//! match-arm range patterns: hex literals make byte-level range
//! patterns readable (`0x30..=0x39` instead of `48..=57`), and bit
//! operators replace the arithmetic-as-bitop idioms (`byte / 16`,
//! `out_ptr * 4294967296 + len`) that dominate stdlib's
//! `crypto::hex_encode` and the new `stdlib::abi` module.
//!
//! Test surface:
//!   1. Hex literals lex into ordinary `IntLit` values — AST and
//!      type checker never see the radix.
//!   2. The four new operators (`<<`, `>>`, `&`, `|`) compile and
//!      have the expected precedence (bit-or < bit-and < shift <
//!      additive, all below comparison).
//!   3. `&` infix vs `&` borrow-prefix doesn't collide.
//!   4. Bit operators on floats or bools are rejected with T054.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("bit_ops_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

#[test]
fn hex_literal_in_let() {
    let source = r#"
module main;

fn boot() -> i64 {
    let x: i64 = 0xFF;
    let y: i64 = 0xDEADBEEF;
    return x + y;
}
"#;
    assert_compiles_clean(source, "hex_let");
}

#[test]
fn hex_literal_in_range_pattern() {
    // The point of hex literals: byte-level range arms read as ASCII
    // codes, not magic decimals. Pairs with the match-range patterns
    // from PR #32.
    let source = r#"
module main;

fn classify(b: i64) -> i64 {
    match b {
        0x30..=0x39 => { return 1; },
        0x41..=0x46 => { return 2; },
        0x61..=0x66 => { return 3; },
        _ => { return 0; },
    }
}
"#;
    assert_compiles_clean(source, "hex_range");
}

#[test]
fn shift_left_and_right() {
    let source = r#"
module main;

fn boot() -> i64 {
    let a: i64 = 1 << 8;
    let b: i64 = 256 >> 1;
    return a + b;
}
"#;
    assert_compiles_clean(source, "shifts");
}

#[test]
fn bit_and_and_or() {
    let source = r#"
module main;

fn boot() -> i64 {
    let masked: i64 = 0xFF & 0x0F;
    let combined: i64 = 0xF0 | 0x0F;
    return masked + combined;
}
"#;
    assert_compiles_clean(source, "bitand_bitor");
}

#[test]
fn packed_ptr_pack_and_unpack_via_bitops() {
    // The motivating use case for the bit-op precedence chain:
    // packing and unpacking the FFI ABI's (ptr, len) i64 by
    // shifting and masking, instead of the `* 4294967296 + len`
    // arithmetic idiom. Mirrors what the new abi.sigil module
    // expresses. Sigil has no parenthesized expressions today, so
    // the chain relies on precedence: `<<` binds tighter than `|`,
    // so `p << 32 | l` parses as `(p << 32) | l`.
    let source = r#"
module main;

fn pack(p: i64, l: i64) -> i64 {
    return p << 32 | l;
}

fn unpack_ptr(packed: i64) -> i64 {
    return packed >> 32;
}

fn unpack_len(packed: i64) -> i64 {
    return packed & 0xFFFFFFFF;
}
"#;
    assert_compiles_clean(source, "packed");
}

#[test]
fn bit_op_precedence_vs_comparison() {
    // Bit operators bind tighter than `==`, so `a & b == c` parses as
    // `(a & b) == c` (the Rust/C convention). If precedence were
    // reversed the example below would be a type error (i64 vs bool).
    let source = r#"
module main;

fn is_low_nibble_zero(b: i64) -> bool {
    return b & 0x0F == 0;
}
"#;
    assert_compiles_clean(source, "prec_cmp");
}

#[test]
fn additive_binds_tighter_than_shift() {
    // Standard C / Rust precedence: `+` is tighter than `<<`, so
    // `a + b << 4` parses as `(a + b) << 4`. Smoke test that the
    // chain reaches both layers.
    let source = r#"
module main;

fn assemble(hi: i64, lo: i64) -> i64 {
    return lo + hi << 8;
}
"#;
    assert_compiles_clean(source, "prec_shift_add");
}

#[test]
fn bit_and_infix_does_not_collide_with_borrow_prefix() {
    // `&` is a borrow prefix at the start of an expression and bit-and
    // when infix. The disambiguation is positional: `parse_prefix_expr`
    // only consumes `&` at the START of an expression. Both shapes
    // need to coexist in the same program.
    let source = r#"
module main;

cap type Fuel { burn }

fn use_borrow(f: &Fuel) -> i64 {
    return 0;
}

fn boot(f: Fuel) -> i64 {
    let mask: i64 = 0xFF & 0x0F;
    let _ = use_borrow(&f);
    return mask;
}
"#;
    assert_compiles_clean(source, "amp_disambig");
}

#[test]
fn bit_op_on_float_is_t054() {
    let source = r#"
module main;

fn boot() -> f64 {
    let a: f64 = 1.5;
    let b: f64 = 0.5;
    return a & b;
}
"#;
    let err = compile_named_module("bit_op_float.sigil", source)
        .expect_err("bit-and on f64 should be rejected");
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&"T054"),
        "expected T054 in diagnostics, got: {codes:?}"
    );
}
