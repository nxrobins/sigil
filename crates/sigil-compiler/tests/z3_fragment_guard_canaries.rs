//! Canaries for the SMT fragment guard (`z3_fragment_guard.rs`).
//!
//! Each negative canary builds ONE out-of-fragment formula via the raw
//! z3 API and matches the EXACT `FragmentViolation` variant — `is_err()`
//! alone is forbidden (ET-Z5), so a guard that over-rejects for the
//! wrong reason cannot hide behind a green canary. The positive controls
//! replicate the three production query families plus site 3's shape
//! (BV and Int constraints as SEPARATE assertions in ONE solver), so an
//! over-rejecting guard dies here too.
//!
//! See `docs/specs/z3-fragment-guard.md` §7.
#![cfg(feature = "solver")]

use std::collections::BTreeSet;

use sigil_compiler::z3_fragment_guard::{
    FragmentViolation, NODE_CEILING, allowed_decl_kind_names, check_fragment,
};
use z3::ast::{Array, Ast, BV, Bool, Int, Real};
use z3::{Config, Context, FuncDecl, Solver, Sort};

fn ctx() -> Context {
    Context::new(&Config::new())
}

// -------------------------------------------------------------------
// Negative canaries — one exact variant per rejection class.
// -------------------------------------------------------------------

/// A quantified formula is rejected as `DisallowedAstKind("Quantifier")`.
/// (A leaked de Bruijn `Var` is unreachable except through a quantifier,
/// which is caught first — this canary covers both.)
#[test]
fn canary_forall_quantifier_rejected() {
    let c = ctx();
    let solver = Solver::new(&c);
    let x = Int::new_const(&c, "x");
    // Sanctioned carve-out: the canary must CONSTRUCT a quantifier to
    // prove the guard rejects one. See clippy.toml's census note.
    #[allow(clippy::disallowed_methods)]
    let q = z3::ast::forall_const(&c, &[&x], &[], &x.ge(&Int::from_i64(&c, 0)));
    solver.assert(&q);

    match check_fragment(&solver) {
        Err(FragmentViolation::DisallowedAstKind { kind, .. }) => {
            assert_eq!(kind, "Quantifier");
        }
        other => panic!("expected DisallowedAstKind(Quantifier), got {other:?}"),
    }
}

/// A Real-sorted term is rejected. The GT op itself is allowlisted (it
/// is the same DeclKind Int comparisons use), so the SORT check is the
/// load-bearing line here — pinned per AG-Z1 as whatever the walk
/// actually produces, which is `DisallowedSort("Real")`.
#[test]
fn canary_real_sort_rejected() {
    let c = ctx();
    let solver = Solver::new(&c);
    let r = Real::new_const(&c, "r");
    solver.assert(&r.gt(&Real::from_real(&c, 1, 2)));

    match check_fragment(&solver) {
        Err(FragmentViolation::DisallowedSort { sort, .. }) => {
            assert_eq!(sort, "Real");
        }
        other => panic!("expected DisallowedSort(Real), got {other:?}"),
    }
}

/// An array `select` is rejected as `DisallowedOp("SELECT")` — the decl
/// check on the select node fires before its Array-sorted child is ever
/// visited (parent-before-children walk).
#[test]
fn canary_array_select_rejected() {
    let c = ctx();
    let solver = Solver::new(&c);
    let a = Array::new_const(&c, "a", &Sort::int(&c), &Sort::int(&c));
    let i = Int::new_const(&c, "i");
    let j = Int::new_const(&c, "j");
    let selected = a.select(&i).as_int().expect("int-ranged array select");
    solver.assert(&selected._eq(&j));

    match check_fragment(&solver) {
        Err(FragmentViolation::DisallowedOp { decl_kind, .. }) => {
            assert_eq!(decl_kind, "SELECT");
        }
        other => panic!("expected DisallowedOp(SELECT), got {other:?}"),
    }
}

/// An uninterpreted FUNCTION application (arity > 0) is rejected —
/// arity-0 UNINTERPRETED consts are the allowed free variables, so the
/// arity is exactly what separates EUF territory from the fragment.
#[test]
fn canary_uninterpreted_fn_rejected() {
    let c = ctx();
    let solver = Solver::new(&c);
    let f = FuncDecl::new(&c, "f", &[&Sort::int(&c)], &Sort::int(&c));
    let x = Int::new_const(&c, "x");
    let y = Int::new_const(&c, "y");
    let fx = f.apply(&[&x]).as_int().expect("int-ranged application");
    solver.assert(&fx._eq(&y));

    match check_fragment(&solver) {
        Err(FragmentViolation::UninterpretedFunction { name, arity, .. }) => {
            assert_eq!(name, "f");
            assert_eq!(arity, 1);
        }
        other => panic!("expected UninterpretedFunction(f, 1), got {other:?}"),
    }
}

/// A bitvector of width 16 is rejected — the inventory's claim is
/// QF_BV<32> exactly, not QF_BV.
#[test]
fn canary_bv16_rejected() {
    let c = ctx();
    let solver = Solver::new(&c);
    let n = BV::new_const(&c, "n", 16);
    solver.assert(&n._eq(&BV::from_u64(&c, 3, 16)));

    match check_fragment(&solver) {
        Err(FragmentViolation::NonWidth32Bv { width, .. }) => {
            assert_eq!(width, 16);
        }
        other => panic!("expected NonWidth32Bv(16), got {other:?}"),
    }
}

/// Mixing Int and BV atoms in one assertion requires a connective — and
/// every connective is outside the op allowlist, so the rejection
/// surfaces as `DisallowedOp("AND")` at the connective, BEFORE the mix
/// detector could fire. The theory-mix invariant is thus double-covered:
/// the op allowlist (this canary) + the per-assertion mix detector
/// (unit-tested directly in the module, since real walks can't reach it).
#[test]
fn canary_mixed_int_bv_assertion_rejected_at_the_connective() {
    let c = ctx();
    let solver = Solver::new(&c);
    let x = Int::new_const(&c, "x");
    let b = BV::new_const(&c, "b", 32);
    let int_atom = x.gt(&Int::from_i64(&c, 0));
    let bv_atom = b.bvule(&BV::from_u64(&c, 7, 32));
    solver.assert(&Bool::and(&c, &[&int_atom, &bv_atom]));

    match check_fragment(&solver) {
        Err(FragmentViolation::DisallowedOp { decl_kind, .. }) => {
            assert_eq!(decl_kind, "AND");
        }
        other => panic!("expected DisallowedOp(AND), got {other:?}"),
    }
}

/// A formula deeper than the node ceiling is rejected as `TooLarge` —
/// built from allowlisted ops only (a `not` chain), so nothing but the
/// ceiling can catch it (ET-Z8: the walk is iterative, so this returns
/// a violation rather than overflowing a recursion stack).
#[test]
fn canary_too_large_rejected() {
    let c = ctx();
    let solver = Solver::new(&c);
    let mut b = Bool::new_const(&c, "b");
    for _ in 0..=NODE_CEILING {
        b = b.not();
    }
    solver.assert(&b);

    match check_fragment(&solver) {
        Err(FragmentViolation::TooLarge { nodes }) => {
            assert!(nodes > NODE_CEILING);
        }
        other => panic!("expected TooLarge, got {other:?}"),
    }
}

// -------------------------------------------------------------------
// Positive controls — the three production query families + site 3.
// An over-rejecting guard (the failure mode exact-variant negatives
// can't catch) dies here.
// -------------------------------------------------------------------

fn names(set: &[&str]) -> BTreeSet<String> {
    set.iter().map(|s| (*s).to_string()).collect()
}

/// The authority-mask family (z3_capability.rs Phase 2 + sink checks):
/// `auth = src & mask`, `auth ⊑ src`, and the sink negation
/// `¬(actual & required = required)` — pure QF_BV<32>.
#[test]
fn positive_authority_bv_query_passes() {
    let c = ctx();
    let solver = Solver::new(&c);
    let auth = BV::new_const(&c, "auth_1", 32);
    let src = BV::new_const(&c, "auth_0", 32);
    let mask = BV::from_u64(&c, 0b1010, 32);
    solver.assert(&auth._eq(&src.bvand(&mask)));
    solver.assert(&auth.bvule(&src));
    let required = BV::from_u64(&c, 0b0010, 32);
    solver.assert(&auth.bvand(&required)._eq(&required).not());

    let report = check_fragment(&solver).expect("authority queries are in-fragment");
    assert_eq!(report.assertions_checked, 3);
    assert_eq!(
        report.observed_decl_kinds,
        names(&["BAND", "BNUM", "EQ", "NOT", "ULEQ", "UNINTERPRETED"])
    );
    assert_eq!(report.observed_sort_kinds, names(&["BV", "Bool"]));
}

/// The refinement family (z3_capability.rs `check_refinement`): bind
/// `refine__value` to the literal, assert the negated predicate — pure
/// QF_LIA over one free variable.
#[test]
fn positive_refinement_lia_query_passes() {
    let c = ctx();
    let solver = Solver::new(&c);
    let value = Int::new_const(&c, "refine__value");
    solver.assert(&value._eq(&Int::from_i64(&c, 42)));
    solver.assert(&value.gt(&Int::from_i64(&c, 100)).not());

    let report = check_fragment(&solver).expect("refinement queries are in-fragment");
    assert_eq!(report.assertions_checked, 2);
    assert_eq!(
        report.observed_decl_kinds,
        names(&["ANUM", "EQ", "GT", "NOT", "UNINTERPRETED"])
    );
    assert_eq!(report.observed_sort_kinds, names(&["Bool", "Int"]));
}

/// The legitimacy family (z3_capability.rs Phase 1): propositional Bool
/// equalities + negations over `legit_*` variables.
#[test]
fn positive_legitimacy_bool_query_passes() {
    let c = ctx();
    let solver = Solver::new(&c);
    let a = Bool::new_const(&c, "legit_a");
    let b = Bool::new_const(&c, "legit_b");
    solver.assert(&a._eq(&b));
    solver.assert(&a.not());

    let report = check_fragment(&solver).expect("legitimacy queries are in-fragment");
    assert_eq!(report.assertions_checked, 2);
    assert_eq!(
        report.observed_decl_kinds,
        names(&["EQ", "NOT", "UNINTERPRETED"])
    );
    assert_eq!(report.observed_sort_kinds, names(&["Bool"]));
}

/// Site 3's shape (the Phase 1+2 consistency probe): ONE solver holding
/// Bool legitimacy, Int fuel, AND BV<32> authority constraints — as
/// SEPARATE assertions. The theory-disjointness invariant is
/// per-ASSERTION (inventory §4), so this MUST pass: it is the test that
/// makes a per-solver mix check unshippable on day one (ET-Z5).
#[test]
fn positive_site3_mixed_solver_separate_assertions_passes() {
    let c = ctx();
    let solver = Solver::new(&c);
    // Phase 1: legitimacy (Bool) + fuel balance (Int).
    let legit_a = Bool::new_const(&c, "legit_a");
    let legit_b = Bool::new_const(&c, "legit_b");
    solver.assert(&legit_a._eq(&legit_b));
    let fuel_parent = Int::new_const(&c, "fuel_parent");
    let fuel_child = Int::new_const(&c, "fuel_child");
    solver.assert(&fuel_child.le(&fuel_parent));
    solver.assert(&fuel_child.ge(&Int::from_i64(&c, 0)));
    // Phase 2: authority (BV<32>).
    let auth = BV::new_const(&c, "auth_1", 32);
    let src = BV::new_const(&c, "auth_0", 32);
    solver.assert(&auth._eq(&src.bvand(&BV::from_u64(&c, 0xFF, 32))));
    solver.assert(&auth.bvule(&src));

    let report = check_fragment(&solver).expect(
        "BV and Int constraints as SEPARATE assertions in one solver are \
         in-fragment — the mix invariant is per-assertion",
    );
    assert_eq!(report.assertions_checked, 5);
    assert_eq!(report.observed_sort_kinds, names(&["BV", "Bool", "Int"]));
}

// -------------------------------------------------------------------
// The chokepoint (ET-Z6) + the pre-lookup ordering witness (ET-Z5).
// ONE test fn: cache stats are process-global, and a second
// stats-reading test in this binary would race it.
// -------------------------------------------------------------------

/// ET-Z6 at the chokepoint: an out-of-fragment query cannot obtain a
/// verdict through the only production route to one — `check_cached`
/// returns `Err` (which the dispatch sites are TYPE-FORCED to handle:
/// `check_cached_solver` returns `Result`, so a site ignoring the
/// violation does not compile; cap-flow sites push C005, refinement
/// sites ICE). And ET-Z5's ordering witness: the guard runs BEFORE any
/// cache interaction — hit/miss counters do not move on a rejection.
/// (A "dirty cache hit" is unconstructible — the key is the SHA256 of
/// the canonical assertions — so stats are the honest witness.)
#[test]
fn guard_err_blocks_the_verdict_with_no_cache_interaction() {
    use sigil_compiler::z3_cache::{Verdict, check_cached, fresh_check, stats_snapshot};

    let c = ctx();

    // Warm path control: a clean query misses then hits.
    let clean = Solver::new(&c);
    let x = Int::new_const(&c, "ordering_witness_var");
    clean.assert(&x.gt(&Int::from_i64(&c, 41)));
    let v1 = check_cached(&clean, fresh_check).expect("fragment-clean query");
    assert_eq!(v1, Verdict::Sat);
    let v2 = check_cached(&clean, |_| panic!("second call must be a cache hit"))
        .expect("fragment-clean query");
    assert_eq!(v2, Verdict::Sat);

    // The rejection: stats must not move at all.
    let (h_before, m_before) = stats_snapshot();
    let dirty = Solver::new(&c);
    let r = Real::new_const(&c, "ordering_witness_real");
    dirty.assert(&r.gt(&Real::from_real(&c, 1, 2)));
    match check_cached(&dirty, fresh_check) {
        Err(FragmentViolation::DisallowedSort { sort, .. }) => assert_eq!(sort, "Real"),
        other => panic!("expected Err(DisallowedSort(Real)) at the chokepoint, got {other:?}"),
    }
    let (h_after, m_after) = stats_snapshot();
    assert_eq!(
        (h_before, m_before),
        (h_after, m_after),
        "a guard rejection must touch NO cache state — the walk runs \
         before any lookup or store"
    );
}

/// The allowlist-as-data is exactly the 13 documented names — the
/// manifest test (PR-2) pins observed ∪ {TRUE, FALSE} against this.
#[test]
fn allowlist_is_exactly_the_documented_thirteen() {
    assert_eq!(
        allowed_decl_kind_names(),
        names(&[
            "ANUM",
            "BAND",
            "BNUM",
            "EQ",
            "FALSE",
            "GE",
            "GT",
            "LE",
            "LT",
            "NOT",
            "TRUE",
            "ULEQ",
            "UNINTERPRETED",
        ])
    );
}
