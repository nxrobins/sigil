//! Phase 2H Phase B — `declassify_ct` + CT intrinsics tests.
//!
//! Covers the @SecretCT → @Secret → @Public two-step declassification
//! ladder, the three branch-free CT intrinsics (`ct_eq`, `ct_select`,
//! `ct_lt`), and basic input-validation diagnostics, including the 8-byte
//! operand width their i64 lowering requires.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;
use sigil_test_utils::pipeline::compile_error_codes;
use wasm_encoder::{
    CodeSection, Function, FunctionSection, Instruction, Module, TypeSection, ValType,
};

fn assert_has_code(err: &CompileError, code: &str) {
    let codes: Vec<&str> = err
        .diagnostics()
        .iter()
        .map(|d| d.code().as_str())
        .collect();
    assert!(
        codes.contains(&code),
        "expected diagnostic {code} but got: {:?}",
        err.diagnostics()
    );
}

// ── declassify_ct two-step chain ──

#[test]
fn declassify_ct_chain_compiles() {
    // @SecretCT → @Secret → @Public via declassify_ct + declassify, each
    // consuming its own linear capability.
    let source = r#"module ext;
cap type DeclassifyCT {}
cap type Declassify {}
fn f(s: i64 @SecretCT, c: DeclassifyCT, d: Declassify) -> i64 @Public {
    let mid: i64 @Secret = declassify_ct(s, c);
    return declassify(mid, d);
}
"#;
    compile_named_module("phase_b_chain.sigil", source)
        .expect("declassify_ct then declassify should compile");
}

#[test]
fn declassify_ct_rejects_wrong_cap_type() {
    let source = r#"module ext;
cap type DeclassifyCT {}
cap type Declassify {}
fn f(s: i64 @SecretCT, c: Declassify) -> i64 @Secret {
    return declassify_ct(s, c);
}
"#;
    let err = compile_named_module("phase_b_wrong_cap.sigil", source)
        .expect_err("declassify_ct with wrong cap type should be rejected");
    // T110 is main's existing cap-type-mismatch code (shared with declassify).
    assert_has_code(&err, "T110");
}

#[test]
fn declassify_ct_rejects_non_secret_ct_input() {
    // declassify_ct on @Public/@Internal/@Secret is rejected (T032).
    // Users should use plain `declassify` for @Secret → @Public.
    let source = r#"module ext;
cap type DeclassifyCT {}
fn f(s: i64 @Secret, c: DeclassifyCT) -> i64 @Secret {
    return declassify_ct(s, c);
}
"#;
    let err = compile_named_module("phase_b_non_ct_input.sigil", source)
        .expect_err("declassify_ct on non-@SecretCT value should be rejected");
    assert_has_code(&err, "T032");
}

// ── CT011: declassify capability linearity (F002 regression) ──
//
// `declassify`/`declassify_ct` consume a LINEAR capability — spec
// `secret-ct.md` §3.4 ("one use per construction") and the CT011 attack row
// ("declassify_ct cap reused → O001"). Before F002 the AIR lowering dropped
// the cap operand entirely, so the ownership pass never saw it and a single
// owned cap could declassify unbounded secrets with a clean compile. These
// pin the reuse → O001 contract; `declassify_ct_chain_compiles` above is the
// paired positive (each cap used exactly once still compiles).

#[test]
fn declassify_cap_reuse_rejected() {
    // One owned `Declassify` cap, two `declassify` calls → O001.
    let source = r#"module ext;
cap type Declassify {}
fn f(s1: i64 @Secret, s2: i64 @Secret, d: Declassify) -> i64 @Public {
    let _a: i64 @Public = declassify(s1, d);
    return declassify(s2, d);
}
"#;
    let err = compile_named_module("f002_declassify_reuse.sigil", source)
        .expect_err("reusing one Declassify cap for two declassify calls must be rejected");
    assert_has_code(&err, "O001");
}

#[test]
fn declassify_ct_cap_reuse_rejected() {
    // One owned `DeclassifyCT` cap, two `declassify_ct` calls → O001.
    let source = r#"module ext;
cap type DeclassifyCT {}
fn f(s1: i64 @SecretCT, s2: i64 @SecretCT, c: DeclassifyCT) -> i64 @Secret {
    let _mid: i64 @Secret = declassify_ct(s1, c);
    return declassify_ct(s2, c);
}
"#;
    let err = compile_named_module("f002_declassify_ct_reuse.sigil", source)
        .expect_err("reusing one DeclassifyCT cap for two declassify_ct calls must be rejected");
    assert_has_code(&err, "O001");
}

#[test]
fn declassify_then_pass_cap_rejected() {
    // Sharper control: `declassify` must actually CONSUME its cap. After a
    // declassify, passing the same cap to any callee is a use-after-move.
    // Pre-F002 this compiled clean (declassify consumed nothing, so the call
    // looked like the first move).
    let source = r#"module ext;
cap type Declassify {}
fn take(d: Declassify) -> i64 @Public { return 0; }
fn f(s1: i64 @Secret, d: Declassify) -> i64 @Public {
    let _a: i64 @Public = declassify(s1, d);
    return take(d);
}
"#;
    let err = compile_named_module("f002_declassify_then_pass.sigil", source)
        .expect_err("using a Declassify cap after declassify consumed it must be rejected");
    assert_has_code(&err, "O001");
}

// ── CT017 reconfirmed under Phase B ──

#[test]
fn ct017_declassify_of_secret_ct_input_rejected() {
    // The existing `declassify` rejects @SecretCT inputs; the user
    // must run declassify_ct first (T031 / CT017).
    let source = r#"module ext;
cap type Declassify {}
fn f(s: i64 @SecretCT, c: Declassify) -> i64 @Public {
    return declassify(s, c);
}
"#;
    let err = compile_named_module("phase_b_ct017.sigil", source)
        .expect_err("declassify of @SecretCT input should be rejected (CT017 / T031)");
    assert_has_code(&err, "T031");
}

// ── CT intrinsics: positive ──

#[test]
fn ct_eq_on_secret_ct_compiles() {
    let source = r#"#[ring(outer)] module ext;
fn cmp(a: i64 @SecretCT, b: i64 @SecretCT) -> bool @SecretCT ! {} {
    return ct_eq(a, b);
}
"#;
    compile_named_module("phase_b_ct_eq.sigil", source).expect("ct_eq on @SecretCT should compile");
}

#[test]
fn ct_select_on_secret_ct_compiles() {
    let source = r#"#[ring(outer)] module ext;
fn pick(c: bool @SecretCT, t: i64 @SecretCT, f: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return ct_select(c, t, f);
}
"#;
    compile_named_module("phase_b_ct_select.sigil", source)
        .expect("ct_select on @SecretCT should compile");
}

#[test]
fn ct_lt_on_secret_ct_compiles() {
    let source = r#"#[ring(outer)] module ext;
fn less(a: i64 @SecretCT, b: i64 @SecretCT) -> bool @SecretCT ! {} {
    return ct_lt(a, b);
}
"#;
    compile_named_module("phase_b_ct_lt.sigil", source).expect("ct_lt on @SecretCT should compile");
}

// ── CT intrinsics: negative ──

#[test]
fn ct_eq_wrong_arity_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(a: i64 @SecretCT) -> bool @SecretCT ! {} {
    return ct_eq(a);
}
"#;
    let err = compile_named_module("phase_b_ct_eq_arity.sigil", source)
        .expect_err("ct_eq with 1 arg should be rejected");
    // T074 is the existing arity-mismatch code for intrinsics.
    assert_has_code(&err, "T074");
}

#[test]
fn ct_select_wrong_cond_type_rejected() {
    let source = r#"#[ring(outer)] module ext;
fn f(c: i64 @SecretCT, t: i64 @SecretCT, e: i64 @SecretCT) -> i64 @SecretCT ! {} {
    return ct_select(c, t, e);
}
"#;
    let err = compile_named_module("phase_b_ct_select_cond.sigil", source)
        .expect_err("ct_select with i64 cond should be rejected");
    // T075 is the existing per-intrinsic arg-type code.
    assert_has_code(&err, "T075");
}

// ── CT intrinsics: operand width ──
//
// `ct_eq`, `ct_lt` and `ct_select` lower to fixed i64 sequences over their operand locals as
// given (`wasm.rs`). The checker once required only a machine integer, so a 4-byte operand
// passed every gate and reached `i64.xor`, `i64.sub` or the i64 select mask as an i32 local:
// `sigil check` printed "Compiled" and wasmtime refused the module. That failed closed, but an
// accepted program must produce a module that validates. A 4-byte operand is now T075, on that
// operand, with the widening that fixes it as the hint (`is_ct_operand_type` in
// `type_check/expressions/intrinsics.rs` says why refuse rather than widen).
//
// Pinned below over every operand width the checker admits as a machine integer, in both
// operand positions of all three intrinsics: a program is accepted exactly when each operand is
// 8 bytes wide or a literal and, for `ct_lt`, the two operands share a signedness; an accepted
// program's module validates; a rejected one carries exactly one T075 per 4-byte operand, on that
// operand, or one on the call for a `ct_lt` pair of one `i64` and one `u64`. "Every accepted
// module validates" is an absence claim, so the validator is first shown refusing the defect's
// own shape (SC-P4, no assertion of absence without an anti-stub). The corpus pair is
// `tests/reject/ct_narrow_operand.sigil` and its accept twin
// `tests/compile/ct_wide_operands.sigil`; running widened operands is
// `sigil-runtime/tests/int_convert.rs`.

/// The operand forms the checker admits as machine integers: a binding of each width, then an
/// integer literal (`None`), which defaults to `i64`.
const CT_OPERAND_WIDTHS: &[Option<&str>] =
    &[Some("i32"), Some("u32"), Some("i64"), Some("u64"), None];

/// Each intrinsic as a test program calls it on operands `{a}` and `{b}`, with those operands'
/// 1-based argument numbers and the noun its diagnostic uses for them.
const CT_CALLS: &[(&str, &str, [usize; 2], &str)] = &[
    (
        "ct_eq",
        "ct_select(ct_eq({a}, {b}), 1, 0)",
        [1, 2],
        "arguments",
    ),
    (
        "ct_lt",
        "ct_select(ct_lt({a}, {b}), 1, 0)",
        [1, 2],
        "arguments",
    ),
    (
        "ct_select",
        "ct_select(c, {a}, {b})",
        [2, 3],
        "branch values",
    ),
];

/// The hint every 4-byte-operand T075 carries. Its warning about an `i32` widened by `.as_u64()`
/// is run by `ct_lt_orders_an_i32_widened_to_u64_by_its_unsigned_bits` in
/// `sigil-runtime/tests/int_convert.rs`.
const CT_NARROW_HINT: &str = "`ct_eq`, `ct_lt` and `ct_select` lower to fixed i64 instruction \
    sequences. Widen a 4-byte operand with `.as_i64()` or `.as_u64()` first: both sign-extend an \
    `i32` and zero-extend a `u32`. `ct_lt` needs two operands of one signedness and compares two \
    `u64` as unsigned values, so widen an `i32` with `.as_i64()` to keep its order: a negative \
    `i32` widened by `.as_u64()` orders above every non-negative one.";

/// The hint a T075 carries for a `ct_*` operand that is not an integer the lowering takes: one
/// to replace, not widen.
const CT_NON_INTEGER_HINT: &str = "`ct_eq`, `ct_lt` and `ct_select` lower to fixed i64 \
    instruction sequences, so each operand must be an `i64`, a `u64` or an integer literal no \
    larger than `i64::MAX`.";

/// The hint a T075 carries for a `ct_lt` literal operand that does not fit the other operand's
/// type: a negative literal beside a `u64`.
const CT_LT_LITERAL_RANGE_HINT: &str = "`ct_lt` gives an integer literal the other operand's \
    type, and this one does not fit it: a `u64` has no negative value. To compare signed values, \
    convert the `u64` operand with `.as_i64()`.";

/// The hint a T075 carries for a `ct_lt` pair of one `i64` and one `u64`.
const CT_LT_MIXED_HINT: &str = "`ct_lt` compares two `i64` operands as signed values and two \
    `u64` operands as unsigned values, so a mixed pair has no single order. Convert one operand \
    with `.as_i64()` or `.as_u64()`: the conversion keeps all 64 bits and picks the order.";

/// The message a T075 carries for a `ct_lt` pair of `lhs` and `rhs`, one `i64` and one `u64`.
fn ct_lt_mixed_message(lhs: &str, rhs: &str) -> String {
    format!(
        "intrinsic `ct_lt` expects two operands of one signedness (two `i64` or two `u64`), \
         found `{lhs}` and `{rhs}`"
    )
}

/// A module of one function that hands two locals of type `local` to `i64.xor` and returns the
/// result: the code a 4-byte `ct_eq` operand produced when `local` is `I32`.
fn xor_of_two_locals(local: ValType) -> Vec<u8> {
    let mut types = TypeSection::new();
    types.ty().function([], [ValType::I64]);
    let mut functions = FunctionSection::new();
    functions.function(0);
    let mut body = Function::new([(2, local)]);
    body.instruction(&Instruction::LocalGet(0));
    body.instruction(&Instruction::LocalGet(1));
    body.instruction(&Instruction::I64Xor);
    body.instruction(&Instruction::End);
    let mut code = CodeSection::new();
    code.function(&body);
    let mut module = Module::new();
    module.section(&types).section(&functions).section(&code);
    module.finish()
}

#[test]
fn wasm_validator_refuses_i32_locals_fed_to_i64_xor() {
    assert!(
        wasmparser::validate(&xor_of_two_locals(ValType::I64)).is_ok(),
        "the i64 twin of the planted module must validate, or the refusal below proves nothing"
    );
    assert!(
        wasmparser::validate(&xor_of_two_locals(ValType::I32)).is_err(),
        "anti-stub: the validator must refuse i32 locals fed to i64.xor, the shape a 4-byte ct_eq \
         operand produced"
    );
}

#[test]
fn ct_operands_narrower_than_8_bytes_are_rejected_and_every_accepted_module_validates() {
    let (mut accepted, mut rejected) = (0, 0);
    for (name, call, arg_numbers, noun) in CT_CALLS {
        for lhs in CT_OPERAND_WIDTHS {
            for rhs in CT_OPERAND_WIDTHS {
                let label = format!("{name} on ({lhs:?}, {rhs:?})");
                let mut decls = String::new();
                let mut operands = Vec::new();
                // Each refused operand's (or pair's) text, and the message and hint its T075
                // must carry.
                let mut want = Vec::new();
                for (slot, width) in [lhs, rhs].into_iter().enumerate() {
                    let Some(ty) = width else {
                        operands.push("3".to_string());
                        continue;
                    };
                    let binding = format!("x{slot}");
                    decls.push_str(&format!("    let {binding}: {ty} = 3;\n"));
                    if matches!(*ty, "i32" | "u32") {
                        want.push((
                            binding.clone(),
                            format!(
                                "intrinsic `{name}` expects 8-byte integer {noun} (`i64` or \
                                 `u64`), arg #{} is `{ty}`",
                                arg_numbers[slot]
                            ),
                            CT_NARROW_HINT,
                        ));
                    }
                    operands.push(binding);
                }
                // Two 8-byte operands of different signedness: `ct_lt` has no order for them.
                if *name == "ct_lt"
                    && let (Some(l @ ("i64" | "u64")), Some(r @ ("i64" | "u64"))) = (lhs, rhs)
                    && l != r
                {
                    want.push((
                        format!("ct_lt({}, {})", operands[0], operands[1]),
                        ct_lt_mixed_message(l, r),
                        CT_LT_MIXED_HINT,
                    ));
                }
                let call = call
                    .replace("{a}", &operands[0])
                    .replace("{b}", &operands[1]);
                let src = format!(
                    "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n\
                     {decls}    let c: bool = input_len > 2;\n    return {call};\n}}\n"
                );
                match compile_named_module("phase_b_ct_operand_width.sigil", &src) {
                    Ok(compiled) => {
                        assert!(
                            want.is_empty(),
                            "{label}: a 4-byte operand or a mixed-signedness ct_lt pair must be \
                             rejected, but the program compiled"
                        );
                        if let Err(e) = wasmparser::validate(&compiled.wasm_inner) {
                            panic!("{label}: accepted, so its module must validate: {e}");
                        }
                        accepted += 1;
                    }
                    Err(err) => {
                        assert_eq!(
                            compile_error_codes(&err),
                            vec!["T075"; want.len()],
                            "{label}: one intrinsic argument-type code per 4-byte operand or \
                             mixed ct_lt pair, and nothing else"
                        );
                        let got: Vec<(String, String, &str)> = err
                            .diagnostics()
                            .iter()
                            .map(|d| {
                                let span = d.span().expect("an operand diagnostic has a span");
                                (
                                    src[span.start..span.end].to_string(),
                                    d.message().to_string(),
                                    d.hint().expect("a ct_* operand diagnostic has a hint"),
                                )
                            })
                            .collect();
                        assert_eq!(
                            got, want,
                            "{label}: one diagnostic per 4-byte operand, on that operand, or one \
                             on the call for a mixed ct_lt pair"
                        );
                        rejected += 1;
                    }
                }
            }
        }
    }
    // Both verdicts, in the measured split: the 3x3 all-8-byte pairs of each intrinsic accepted
    // but ct_lt's (i64, u64) and (u64, i64), and the other 16 pairs of each rejected. A matrix
    // that lost its 4-byte or mixed rows would pass the loop alone.
    assert_eq!(
        (accepted, rejected),
        (25, 50),
        "the width matrix must exercise both verdicts"
    );
}

#[test]
fn widened_4_byte_ct_operands_compile_and_validate() {
    // The hint's remedy, in all three intrinsics, through both conversions, from both 4-byte
    // widths. `int_convert.rs` runs the orders they give `ct_lt`.
    let source = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: i32 = 0 - 3;
    let b: u32 = 4294967295;
    let same: bool = ct_eq(a.as_u64(), b.as_u64());
    let lt: bool = ct_lt(a.as_i64(), b.as_i64());
    return ct_select(same, a.as_i64(), b.as_u64()) + ct_select(lt, 1, 0);
}
"#;
    let compiled = compile_named_module("phase_b_ct_widened.sigil", source)
        .expect("4-byte operands widened with .as_i64() / .as_u64() must compile");
    wasmparser::validate(&compiled.wasm_inner).expect("the widened program's module must validate");
}

#[test]
fn secret_ct_4_byte_operands_are_accepted_once_widened() {
    // The intrinsics exist for `@SecretCT` data, so the remedy must hold there: widened, the
    // operands compile; as given, they are one T075 each.
    let widened = r#"#[ring(outer)] module ext;
fn cmp(a: i32 @SecretCT, b: i32 @SecretCT) -> bool @SecretCT ! {} {
    return ct_eq(a.as_i64(), b.as_i64());
}
"#;
    let compiled = compile_named_module("phase_b_ct_eq_widened.sigil", widened)
        .expect("ct_eq on widened @SecretCT i32 operands must compile");
    for module in std::iter::once(&compiled.wasm_inner).chain(compiled.wasm_outer.as_ref()) {
        wasmparser::validate(module).expect("the widened program's modules must validate");
    }
    let narrow = widened.replace("a.as_i64(), b.as_i64()", "a, b");
    assert_ne!(narrow, widened, "the rewrite must hit the call");
    let err = compile_named_module("phase_b_ct_eq_narrow.sigil", &narrow)
        .expect_err("ct_eq on @SecretCT i32 operands as given must be rejected");
    assert_eq!(
        compile_error_codes(&err),
        vec!["T075"; 2],
        "one intrinsic argument-type code per 4-byte operand"
    );
}

#[test]
fn ct_non_integer_operand_draws_the_8_byte_message_and_its_own_hint() {
    // A `bool` operand gets the same message as a 4-byte one, so swapping it for an `i32` does
    // not move the caller to a second wording; only the hint differs, since a `bool` is
    // replaced, not widened. So does an integer literal past `i64::MAX`, which is typed `u256`
    // (a negative literal is an integer literal: `ct_lt_refuses_a_negative_literal_beside_a_u64`).
    for (name, call, arg, ty, noun) in [
        ("ct_eq", "ct_eq(flag, 1)", 1, "bool", "arguments"),
        ("ct_lt", "ct_lt(1, flag)", 2, "bool", "arguments"),
        (
            "ct_select",
            "ct_select(true, flag, 1)",
            2,
            "bool",
            "branch values",
        ),
        (
            "ct_lt",
            "ct_lt(input_len, 9223372036854775808)",
            2,
            "u256",
            "arguments",
        ),
    ] {
        let source = format!(
            "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    \
             let flag: bool = input_len > 2;\n    let r = {call};\n    return input_len;\n}}\n"
        );
        let err = compile_named_module("phase_b_ct_non_integer.sigil", source)
            .expect_err("a bool or u256 ct_* operand must be rejected");
        assert_eq!(compile_error_codes(&err), vec!["T075"], "{call}: the code");
        let d = &err.diagnostics()[0];
        assert_eq!(
            d.message(),
            format!(
                "intrinsic `{name}` expects 8-byte integer {noun} (`i64` or `u64`), arg #{arg} \
                 is `{ty}`"
            ),
            "{call}: the message"
        );
        assert_eq!(d.hint(), Some(CT_NON_INTEGER_HINT), "{call}: the hint");
    }
}

#[test]
fn ct_lt_refuses_a_mixed_signedness_pair_and_a_conversion_admits_it() {
    // `ct_lt` compares two `i64` as signed values and two `u64` as unsigned values, so one of
    // each has no single order: one T075 on the call, in either operand order. Converting either
    // operand picks the order and compiles; `ct_eq` takes the same pair, since bit equality has no
    // order to pick.
    for (pair, lhs, rhs, as_signed, as_unsigned) in [
        ("a, b", "i64", "u64", "a, b.as_i64()", "a.as_u64(), b"),
        ("b, a", "u64", "i64", "b.as_i64(), a", "b, a.as_u64()"),
    ] {
        let call = format!("ct_lt({pair})");
        let source = format!(
            "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    \
             let a: i64 = input_len;\n    let b: u64 = 7;\n    let lt: bool = {call};\n    \
             return ct_select(lt, 1, 0);\n}}\n"
        );
        let err = compile_named_module("phase_b_ct_lt_mixed.sigil", &source)
            .expect_err("a mixed-signedness ct_lt pair must be rejected");
        assert_eq!(compile_error_codes(&err), vec!["T075"], "{call}: the code");
        let d = &err.diagnostics()[0];
        assert_eq!(
            d.message(),
            ct_lt_mixed_message(lhs, rhs),
            "{call}: the message"
        );
        assert_eq!(d.hint(), Some(CT_LT_MIXED_HINT), "{call}: the hint");
        let span = d.span().expect("the pair diagnostic has a span");
        assert_eq!(
            &source[span.start..span.end],
            call,
            "{call}: the diagnostic sits on the call"
        );
        for admitted in [
            format!("ct_lt({as_signed})"),
            format!("ct_lt({as_unsigned})"),
            format!("ct_eq({pair})"),
        ] {
            let converted = source.replace(&call, &admitted);
            let compiled = compile_named_module("phase_b_ct_lt_converted.sigil", &converted)
                .unwrap_or_else(|e| panic!("{admitted} must compile: {:?}", e.diagnostics()));
            wasmparser::validate(&compiled.wasm_inner)
                .unwrap_or_else(|e| panic!("{admitted}: the module must validate: {e}"));
        }
    }
}

#[test]
fn ct_lt_refuses_a_negative_literal_beside_a_u64() {
    // `-1` folds to a negative integer literal. Beside a `u64`, `ct_lt` gives it that type, which
    // has no negative value: one T075 on the literal, in either operand order, with a hint of its
    // own. Beside an `i64` the literal fits and compiles, and so does `0 - 1` beside a `u64`:
    // literal arithmetic is checked leaf by leaf, and both leaves fit.
    for call in ["ct_lt(-1, m)", "ct_lt(m, -1)"] {
        let source = format!(
            "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    \
             let m: u64 = 7;\n    let lt: bool = {call};\n    return ct_select(lt, 1, 0);\n}}\n"
        );
        let err = compile_named_module("phase_b_ct_lt_negative_literal.sigil", &source)
            .expect_err("a negative literal beside a u64 ct_lt operand must be rejected");
        assert_eq!(compile_error_codes(&err), vec!["T075"], "{call}: the code");
        let d = &err.diagnostics()[0];
        assert_eq!(
            d.message(),
            "integer literal `-1` is out of range for `u64`",
            "{call}: the message"
        );
        assert_eq!(d.hint(), Some(CT_LT_LITERAL_RANGE_HINT), "{call}: the hint");
        let span = d.span().expect("the literal diagnostic has a span");
        assert_eq!(
            &source[span.start..span.end],
            "-1",
            "{call}: the diagnostic sits on the literal"
        );
        for admitted in [call.replace('m', "input_len"), call.replace("-1", "0 - 1")] {
            let changed = source.replace(call, &admitted);
            assert_ne!(changed, source, "the rewrite must hit the call");
            let compiled = compile_named_module("phase_b_ct_lt_literal_admitted.sigil", &changed)
                .unwrap_or_else(|e| panic!("{admitted} must compile: {:?}", e.diagnostics()));
            wasmparser::validate(&compiled.wasm_inner)
                .unwrap_or_else(|e| panic!("{admitted}: the module must validate: {e}"));
        }
    }
}
