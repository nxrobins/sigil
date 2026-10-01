//! BUG-4 — the QF_LIA fuel family rejects a literal overdraw, **solver-lane half**.
//!
//! `air_capability_v2` asserts, per split/draw site, `dst_fuel == amount`, `src_fuel >= amount`
//! and non-negativity over Int constants named by VarId. Until BUG-4 the amount constant was never
//! bound to anything, so the family was satisfiable for every program and rejected nothing: a chain
//! that draws 20 from a child holding 10 compiled and failed only at run time (`InsufficientFuel`).
//! The fix binds the amount to its numeral when the AIR proves it (a single-definition `IntLit`
//! assignment), so the chain is UNSAT at the phase-3 consistency probe and surfaces as C002.
//!
//! C002 is a Z3 (solver) diagnostic, so this file is gated `#![cfg(feature = "solver")]` and runs
//! ONLY in the `solver` CI lane (`cargo test -p sigil-compiler --features solver`); it contributes 0
//! tests to the workspace `--no-default-features` lane. It drives parse → resolve → type-check →
//! AIR lowering and runs the sole prover `air_capability_v2::verify_air_capabilities` directly
//! (the `lambda_sigil_c003.rs` pattern), asserting EXACT capability-code sets. Every expectation
//! follows from the constraint shape the prover emits:
//!
//! * a bound chain `fuel_a == 10 ∧ fuel_a >= 20` is UNSAT → exactly `{C002}`;
//! * a bound negative literal contradicts `split_amount >= 0` → exactly `{C002}`;
//! * an in-budget chain, a draw from a FREE budget (state field / parameter) and a computed
//!   amount are SAT → no capability code at all.
//!
//! The clean cases are the absence half of the claim; the rejecting cases in the same file are its
//! anti-stub (SC-P4): the detector demonstrably fires on the planted overdraw.

#![cfg(feature = "solver")]

use sigil_compiler::diagnostics::{Diagnostic, Severity};
use sigil_compiler::source::SourceFile;
use sigil_compiler::{
    CompileOptions, air, air_capability_v2, compile_module, name_resolution, parser, type_check,
};

/// Draw 10 from the entry actor's fuel, then 20 from that child: the child's fuel is bound to
/// 10 and the second site demands `fuel_a >= 20`.
const OVERDRAW_CHAIN: &str = "module sigil;\n\
cap type Fuel {}\n\
actor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\n\
entry actor Main {\n\
    state { fuel: Fuel }\n\
    on Start() -> i64 {\n\
        let a = fuel.draw(10);\n\
        let b = a.draw(20);\n\
        let w = spawn::<Worker>(b);\n\
        return 1;\n\
    }\n\
}\n";

/// The amounts of the chain swapped: 20 then 10 — `fuel_a == 20 ∧ fuel_a >= 10` is SAT.
const IN_BUDGET_CHAIN: &str = "module sigil;\n\
cap type Fuel {}\n\
actor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\n\
entry actor Main {\n\
    state { fuel: Fuel }\n\
    on Start() -> i64 {\n\
        let a = fuel.draw(20);\n\
        let b = a.draw(10);\n\
        let w = spawn::<Worker>(b);\n\
        return 1;\n\
    }\n\
}\n";

/// The overdraw amount reaches the draw through a named `let` binding rather than an inline
/// literal. The binding is still a single-definition `IntLit` assignment, so it is bound.
const OVERDRAW_VIA_NAMED_LITERAL: &str = "module sigil;\n\
cap type Fuel {}\n\
actor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\n\
entry actor Main {\n\
    state { fuel: Fuel }\n\
    on Start() -> i64 {\n\
        let n = 20;\n\
        let a = fuel.draw(10);\n\
        let b = a.draw(n);\n\
        let w = spawn::<Worker>(b);\n\
        return 1;\n\
    }\n\
}\n";

/// A negative literal amount type-checks (nothing before the prover rejects it) and lowers to
/// `IntLit(-5)`; bound, it contradicts the family's `split_amount >= 0`.
const NEGATIVE_LITERAL_AMOUNT: &str = "module sigil;\n\
cap type Fuel {}\n\
actor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\n\
entry actor Main {\n\
    state { fuel: Fuel }\n\
    on Start() -> i64 {\n\
        let a = fuel.draw(-5);\n\
        let w = spawn::<Worker>(a);\n\
        return 1;\n\
    }\n\
}\n";

/// `i64::MAX` split straight out of the entry actor's state fuel. The parent's budget is a
/// FREE constant by decision (its value is a run-time fact), so this is SAT at compile time and
/// the runtime table is the enforcement.
const STATE_BUDGET_STAYS_FREE: &str = "module sigil;\n\
cap type Fuel {}\n\
actor Worker { init(f: Fuel) {} on Ping() -> i64 { return 0; } }\n\
entry actor Main {\n\
    state { fuel: Fuel }\n\
    on Start() -> i64 {\n\
        let big = fuel.split(9223372036854775807);\n\
        let w = spawn::<Worker>(big);\n\
        return 1;\n\
    }\n\
}\n";

/// A computed amount (`n * 100`) drawn from a cap PARAMETER inside a plain fn: neither the
/// amount nor the parent budget is a single-definition literal, so both stay free.
const COMPUTED_AMOUNT_STAYS_FREE: &str = "module sigil;\n\
cap type Fuel {}\n\
fn burn(f: Fuel, n: i64) -> i64 {\n\
    let big = n * 100;\n\
    let child = f.draw(big);\n\
    return 0;\n\
}\n\
entry actor Main {\n\
    state { fuel: Fuel }\n\
    on Start() -> i64 {\n\
        let a = fuel.draw(10);\n\
        let r = burn(a, 3);\n\
        return r;\n\
    }\n\
}\n";

/// Sorted, deduplicated capability C-codes among error diagnostics.
fn cap_codes(diags: &[Diagnostic]) -> Vec<String> {
    let mut codes: Vec<String> = diags
        .iter()
        .filter(|d| d.severity() == Severity::Error)
        .map(|d| d.code().as_str().to_string())
        .filter(|c| c.starts_with('C'))
        .collect();
    codes.sort();
    codes.dedup();
    codes
}

/// parse → resolve → type-check → lower → sole prover; the exact C-code set it emits.
fn prover_codes(id: &str, src: &str) -> Vec<String> {
    let source = SourceFile::new(id, src);
    let (ast, pdiags) = parser::parse(&source);
    assert!(
        !pdiags.iter().any(|d| d.severity() == Severity::Error),
        "{id}: source must parse cleanly"
    );
    let resolved =
        name_resolution::resolve(&ast).unwrap_or_else(|_| panic!("{id}: name resolution failed"));
    let (typed, registry) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|d| {
            panic!(
                "{id}: type-check failed: {:?}",
                d.iter().map(|x| x.code().as_str()).collect::<Vec<_>>()
            )
        });
    let air = air::lower(&typed);
    match air_capability_v2::verify_air_capabilities(&air, &registry) {
        Ok(_) => Vec::new(),
        Err(diags) => cap_codes(&diags),
    }
}

#[test]
fn literal_overdraw_chain_is_unsat_and_rejected_with_c002() {
    assert_eq!(
        prover_codes("overdraw-chain", OVERDRAW_CHAIN),
        vec!["C002".to_string()],
        "draw 20 from a child bound to 10: the fuel family must be UNSAT at the consistency probe"
    );
}

#[test]
fn overdraw_through_named_literal_binding_is_rejected_with_c002() {
    assert_eq!(
        prover_codes("overdraw-named-literal", OVERDRAW_VIA_NAMED_LITERAL),
        vec!["C002".to_string()],
        "a single-definition `let n = 20` is a bound literal, not a free amount"
    );
}

#[test]
fn negative_literal_amount_is_rejected_with_c002() {
    assert_eq!(
        prover_codes("negative-literal", NEGATIVE_LITERAL_AMOUNT),
        vec!["C002".to_string()],
        "a bound negative amount contradicts `split_amount >= 0`"
    );
}

#[test]
fn in_budget_chain_verifies_cleanly() {
    assert_eq!(
        prover_codes("in-budget-chain", IN_BUDGET_CHAIN),
        Vec::<String>::new(),
        "draw 10 from a child bound to 20 is SAT; the binding must not over-reject"
    );
}

#[test]
fn state_and_parameter_budgets_stay_free() {
    assert_eq!(
        prover_codes("state-budget-free", STATE_BUDGET_STAYS_FREE),
        Vec::<String>::new(),
        "a state field's budget is a free constant: i64::MAX split from it is SAT (runtime enforces)"
    );
    assert_eq!(
        prover_codes("computed-amount-free", COMPUTED_AMOUNT_STAYS_FREE),
        Vec::<String>::new(),
        "a computed amount drawn from a cap parameter binds nothing: SAT (runtime enforces)"
    );
}

/// End-to-end: the production pipeline (`compile_module`) fails the overdraw chain with C002 —
/// the structural pre-check (C001 territory) passes it, so the rejection is the prover's alone —
/// and accepts the in-budget control. Pins that the direct-prover verdicts above are what a user
/// of `sigil check` sees in the solver lane.
#[test]
fn compile_module_rejects_overdraw_and_accepts_in_budget_control() {
    let Err(err) = compile_module(OVERDRAW_CHAIN) else {
        panic!("the overdraw chain must fail compilation in the solver lane");
    };
    assert_eq!(
        cap_codes(err.diagnostics()),
        vec!["C002".to_string()],
        "compile_module: exactly C002 for the overdraw chain"
    );
    assert!(
        compile_module(IN_BUDGET_CHAIN).is_ok(),
        "compile_module: the in-budget control must compile cleanly"
    );
}
