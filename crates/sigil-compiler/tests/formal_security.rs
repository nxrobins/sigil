use sigil_compiler::{
    CompileOptions, compile_named_module, compile_project, formal::CSIR_MODEL_VERSION,
    source::SourceFile,
};
use sigil_test_utils::snapshot::wat_of;

const SOURCE: &str = r#"
module formal_gate;
cap type Fuel {}
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        if true { return 1; } else { return 0; }
    }
}
"#;

#[test]
fn every_successful_compilation_has_fresh_formal_evidence() {
    let compilation = compile_named_module("formal_gate.sigil", SOURCE).expect("source compiles");
    let report = &compilation.formal_security_report;
    assert_eq!(CSIR_MODEL_VERSION, 9);
    assert_eq!(report.model_version, CSIR_MODEL_VERSION);
    assert_eq!(report.csir_fingerprint.len(), 64);
    assert_eq!(report.checker_source_fingerprint.len(), 64);
    assert!(report.checked_functions > 0);
    assert_eq!(
        report.checked_functions,
        compilation.air.functions.len() as u64,
        "the report's function count must come from the mandatory semantic AIR section"
    );
    assert!(report.checked_nodes >= report.checked_functions);
    assert!(
        report.checked_ct_operations >= 2,
        "the `if` must produce both the constructor census node and a verifier-derived graph CT use"
    );
    assert!(
        report.checked_flows > report.checked_functions,
        "the report must count verifier-owned flow edges/sinks, not only function records"
    );
}

#[test]
fn semantic_literal_payload_changes_the_csir_fingerprint() {
    let first = compile_named_module(
        "semantic_literal.sigil",
        "module semantic_literal; fn answer() -> i64 { return 41; }",
    )
    .expect("first literal compiles");
    let second = compile_named_module(
        "semantic_literal.sigil",
        "module semantic_literal; fn answer() -> i64 { return 42; }",
    )
    .expect("second literal compiles");
    assert_ne!(
        first.formal_security_report.csir_fingerprint,
        second.formal_security_report.csir_fingerprint,
        "resolved semantic literals must be certificate-bound"
    );
}

#[test]
fn v8_preserves_range_and_match_policy_classes_through_air() {
    compile_named_module(
        "semantic_range.sigil",
        r#"
module semantic_range;
fn sum_to(n: i64) -> i64 {
    let mut acc = 0;
    for i in 0..n { acc = acc + i; }
    return acc;
}
"#,
    )
    .expect("range control must retain its T022 policy class through AIR and CSIR v8");

    compile_named_module(
        "semantic_match.sigil",
        r#"
module semantic_match;
fn pick(x: i64) -> i64 {
    match x {
        0 => { return 1; },
        _ => { return 2; },
    }
}
"#,
    )
    .expect("match dispatch must retain its T023 policy class through AIR and CSIR v8");

    compile_named_module(
        "semantic_guarded_match.sigil",
        r#"
module semantic_guarded_match;
enum Choice { A, B }
fn pick(x: Choice, n: i64) -> i64 {
    match x {
        Choice::A if n > 0 => { return 1; },
        _ => { return 2; },
    }
}
"#,
    )
    .expect("match guards must retain branch policy without annotating catch-all jumps");
}

#[test]
fn v8_accepts_the_two_stage_release_chain() {
    compile_named_module(
        "semantic_release.sigil",
        r#"
module semantic_release;
cap type DeclassifyCT {}
cap type Declassify {}
fn release(s: i64 @SecretCT, c: DeclassifyCT, d: Declassify) -> i64 @Public {
    let mid: i64 @Secret = declassify_ct(s, c);
    return declassify(mid, d);
}
"#,
    )
    .expect("both release stages must survive AIR and satisfy the semantic v8 verifier");
}

#[test]
fn v8_records_zero_argument_ffi_as_an_explicit_empty_policy_window() {
    compile_named_module(
        "time.sigil",
        include_str!("../../../stdlib/sigil/time.sigil"),
    )
    .expect("a zero-argument FFI call must carry an explicit empty T027 policy record");
}

#[test]
fn v8_accepts_only_declared_public_or_ct_sources_for_direct_ct_promotion() {
    compile_named_module(
        "semantic_ct_source.sigil",
        r#"
module semantic_ct_source;
fn promote(x: i64 @Public) -> i64 @SecretCT {
    let y: i64 @SecretCT = x;
    return y;
}
fn preserve(x: i64 @SecretCT) -> i64 @SecretCT { return x; }
"#,
    )
    .expect("Public→SecretCT and SecretCT→SecretCT direct sources must carry T030 evidence");
}

#[test]
fn formal_report_and_csir_fingerprint_are_deterministic() {
    let first = compile_named_module("formal_gate.sigil", SOURCE).expect("first compile succeeds");
    let second =
        compile_named_module("formal_gate.sigil", SOURCE).expect("second compile succeeds");
    assert_eq!(first.formal_security_report, second.formal_security_report);
}

#[test]
fn formal_report_is_deterministic_across_multifile_input_order() {
    let math = || {
        SourceFile::new(
            "math.sigil",
            "module math;\npub fn add(a: i64, b: i64) -> i64 { return a + b; }\n",
        )
    };
    let main = || {
        SourceFile::new(
            "main.sigil",
            "module main;\nuse sigil::math;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return math::add(1, 2); }\n",
        )
    };
    let first = compile_project(vec![math(), main()], None, CompileOptions::default())
        .expect("ordered project compiles");
    let reversed = compile_project(vec![main(), math()], None, CompileOptions::default())
        .expect("reversed project compiles");
    assert_eq!(
        first.formal_security_report,
        reversed.formal_security_report
    );
}

#[test]
fn exclusive_branches_may_each_consume_the_same_capability() {
    let source = r#"
module formal_affine_branch;
cap type Fuel { burn }
fn spend(fuel: Fuel) -> i64 { return 1; }
fn choose(fuel: Fuel, take_left: bool) -> i64 {
    if take_left {
        let left: i64 = spend(fuel);
    } else {
        let right: i64 = spend(fuel);
    }
    return 0;
}
"#;
    compile_named_module("formal_affine_branch.sigil", source)
        .expect("mutually exclusive capability consumption must compile");
}

#[test]
fn use_after_a_may_consume_join_keeps_the_source_level_o001() {
    let source = r#"
module formal_affine_join;
cap type Fuel { burn }
fn spend(fuel: Fuel) -> i64 { return 1; }
fn reuse(fuel: Fuel, take_left: bool) -> i64 {
    if take_left {
        let left: i64 = spend(fuel);
    } else {
        let right: i64 = 0;
    }
    return spend(fuel);
}
"#;
    let error = compile_named_module("formal_affine_join.sigil", source)
        .expect_err("may-consumed capability must not be usable after the join");
    let codes: Vec<&str> = error
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert!(codes.contains(&"O001"), "expected O001, got {codes:?}");
    assert!(!codes.contains(&"I013"), "formal gate preempted O001");
}

#[test]
fn loop_backedge_consumption_keeps_the_source_level_o001() {
    let source = r#"
module formal_affine_loop;
cap type Fuel { burn }
fn spend(fuel: Fuel) -> i64 { return 1; }
fn repeat(fuel: Fuel, keep_going: bool) -> i64 {
    while keep_going {
        let used: i64 = spend(fuel);
    }
    return 0;
}
"#;
    let error = compile_named_module("formal_affine_loop.sigil", source)
        .expect_err("a loop back-edge must not make one capability reusable");
    let codes: Vec<&str> = error
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert!(codes.contains(&"O001"), "expected O001, got {codes:?}");
    assert!(!codes.contains(&"I013"), "formal gate preempted O001");
}

#[test]
fn break_consumption_reaches_the_post_loop_ownership_join() {
    let source = r#"
module formal_affine_break;
cap type Fuel { burn }
fn spend(fuel: Fuel) -> i64 { return 1; }
fn reuse(fuel: Fuel, stop: bool) -> i64 {
    while stop {
        let used: i64 = spend(fuel);
        break;
    }
    return spend(fuel);
}
"#;
    let error = compile_named_module("formal_affine_break.sigil", source)
        .expect_err("break-path consumption must make the post-loop use invalid");
    let codes: Vec<&str> = error
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str())
        .collect();
    assert!(codes.contains(&"O001"), "expected O001, got {codes:?}");
    assert!(!codes.contains(&"I013"), "formal gate preempted O001");
}

fn diagnostic_codes(source: &str) -> Vec<String> {
    compile_named_module("quantity_taint.sigil", source)
        .expect_err("quantity taint policy must reject this program")
        .diagnostics()
        .iter()
        .map(|diagnostic| diagnostic.code().as_str().to_owned())
        .collect()
}

#[test]
fn secret_split_amount_keeps_the_source_level_t001() {
    let codes = diagnostic_codes(
        r#"
module quantity_taint;
cap type Fuel {}
fn go(fuel: Fuel, amount: i64 @Secret) -> i64 {
    let child: Fuel = fuel.split(amount);
    return 0;
}
"#,
    );
    assert!(codes.iter().any(|code| code == "T001"), "got {codes:?}");
    assert!(!codes.iter().any(|code| code == "I013"), "got {codes:?}");
}

#[test]
fn secret_ct_draw_amount_keeps_the_source_level_t027() {
    let codes = diagnostic_codes(
        r#"
module quantity_taint;
cap type Fuel {}
fn go(fuel: Fuel, amount: i64 @SecretCT) -> i64 {
    let child: Fuel = fuel.draw(amount);
    return 0;
}
"#,
    );
    assert!(codes.iter().any(|code| code == "T027"), "got {codes:?}");
    assert!(!codes.iter().any(|code| code == "I013"), "got {codes:?}");
}

#[test]
fn public_amount_under_secret_pc_keeps_the_source_level_t001() {
    let codes = diagnostic_codes(
        r#"
module quantity_taint;
cap type Fuel {}
fn go(fuel: Fuel, amount: i64, secret: bool @Secret) -> i64 {
    if secret {
        let child: Fuel = fuel.split(amount);
    }
    return 0;
}
"#,
    );
    assert!(codes.iter().any(|code| code == "T001"), "got {codes:?}");
    assert!(!codes.iter().any(|code| code == "I013"), "got {codes:?}");
}

#[test]
fn negative_public_amount_compiles_with_an_unconditional_signed_wasm_guard() {
    let compilation = compile_named_module(
        "negative_quantity.sigil",
        r#"
module negative_quantity;
cap type Fuel {}
fn go(fuel: Fuel) -> i64 {
    let child: Fuel = fuel.split(-1);
    return 0;
}
"#,
    )
    .expect("negative Public quantities are guarded runtime traps, not compile-time rejection");
    let wat = wat_of(&compilation.wasm_inner);
    assert!(wat.contains("i64.lt_s"), "signed guard absent:\n{wat}");
    assert!(wat.contains("unreachable"), "guard trap absent:\n{wat}");
}
