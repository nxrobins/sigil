//! The runtime SMT fragment guard.
//!
//! Walks every assertion of a [`z3::Solver`] and rejects anything outside
//! the decidable fragment documented in `docs/z3-theory-inventory.md` §4
//! (QF_BV<32> authority masks, QF_LIA fuel/refinements, and propositional
//! Bool legitimacy, theory-disjoint per assertion). The complete contract lives in
//! `docs/specs/z3-fragment-guard.md`.
//!
//! Load-bearing properties:
//!
//! 1. **Import isolation.** This module imports `z3` and `std` only, never
//!    `z3_capability`, `z3_cache`, or `type_check`, so both query paths
//!    can call it without coupling. Grep-fenced.
//! 2. **Bounded walk.** The walk is an iterative worklist (no
//!    recursion) with a hard [`NODE_CEILING`]; breach yields
//!    [`FragmentViolation::TooLarge`], never a hang or stack overflow.
//!    The ceiling is also the cost bound — no other performance claim is
//!    made.
//! 3. **Default-reject (the allowlist's `_` arm).** Unlike the repo's
//!    no-`_` accept-map drift-locks, the `DeclKind` enum is owned by
//!    z3-sys (~250 variants, we use 13), so the fail-safe direction is
//!    reversed: an unanticipated op must REJECT at runtime, not
//!    compile-error the guard. A z3 version bump adding variants changes
//!    nothing — unknown ops stay rejected.
//! 4. **Verdicts are pure; recording is separate.** [`check_fragment`]
//!    is a deterministic function of the assertion set with no global
//!    effects. The observation accumulator is fed ONLY by the production
//!    chokepoints via [`record_observations`], so canary tests never
//!    pollute the exactness manifest. Recording is order-independent
//!    because `BTreeSet` union commutes.

use std::collections::{BTreeSet, HashSet};
use std::fmt;
use std::sync::{Mutex, OnceLock};

use z3::ast::{Ast, Dynamic};
use z3::{AstKind, DeclKind, Solver, SortKind};

/// Hard bound on visited nodes per [`check_fragment`] call.
/// Production queries measure in dozens of nodes; ~1000× headroom. The
/// guard exists to catch future buggy builders, and a buggy builder is
/// exactly what produces a formula deep enough to overflow a recursive
/// walker — so the walk is iterative and this ceiling is the only limit.
pub const NODE_CEILING: usize = 100_000;

/// Truncation bound for the offending-term rendering carried inside a
/// violation. Mirrors the z3_cache log-prefix discipline: enough to
/// identify the term, never megabytes. [`FragmentViolation::TooLarge`]
/// deliberately carries NO rendering — formatting a ceiling-sized term
/// would be the very cost the ceiling exists to avoid.
const SNIPPET_MAX_CHARS: usize = 200;

/// Why an assertion left the decidable fragment. Each variant names the
/// offending op/sort and carries a truncated rendering of the offending
/// node (not the whole assertion — the node is the evidence).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FragmentViolation {
    /// AstKind other than Numeral/App: `Var` is a leaked de Bruijn bound
    /// variable (i.e. a quantifier body), `Quantifier` is a quantifier,
    /// `Sort`/`FuncDecl`/`Unknown` are not terms at all.
    DisallowedAstKind { kind: String, node: String },
    /// DeclKind outside the allowlist (e.g. "AND", "SELECT", "ADD").
    DisallowedOp {
        decl_kind: String,
        decl_name: String,
        node: String,
    },
    /// UNINTERPRETED with arity > 0 — an uninterpreted FUNCTION
    /// application (EUF territory; free CONSTANTS are arity 0).
    UninterpretedFunction {
        name: String,
        arity: usize,
        node: String,
    },
    /// Sort outside {Bool, Int, BV} (e.g. "Real", "Array", "Datatype").
    DisallowedSort { sort: String, node: String },
    /// BV sort with width != 32 (the inventory's QF_BV<32> claim).
    NonWidth32Bv { width: u32, node: String },
    /// One assertion contains both Int-sorted and BV-sorted subterms —
    /// the theory-disjointness invariant (inventory §4). Bool does not
    /// count: the shared propositional skeleton is explicitly fine.
    MixedTheories { node: String },
    /// The walk visited more than [`NODE_CEILING`] nodes (ET-Z8).
    TooLarge { nodes: usize },
}

impl fmt::Display for FragmentViolation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FragmentViolation::DisallowedAstKind { kind, node } => {
                write!(f, "disallowed AST node kind {kind} in `{node}`")
            }
            FragmentViolation::DisallowedOp {
                decl_kind,
                decl_name,
                node,
            } => {
                write!(f, "disallowed op {decl_kind} (`{decl_name}`) in `{node}`")
            }
            FragmentViolation::UninterpretedFunction { name, arity, node } => {
                write!(
                    f,
                    "uninterpreted function `{name}` of arity {arity} in `{node}`"
                )
            }
            FragmentViolation::DisallowedSort { sort, node } => {
                write!(f, "disallowed sort {sort} in `{node}`")
            }
            FragmentViolation::NonWidth32Bv { width, node } => {
                write!(f, "bitvector of width {width} (only BV<32>) in `{node}`")
            }
            FragmentViolation::MixedTheories { node } => {
                write!(
                    f,
                    "Int and BV subterms mixed in one assertion `{node}` \
                     (theory-disjointness invariant)"
                )
            }
            FragmentViolation::TooLarge { nodes } => {
                write!(
                    f,
                    "assertion walk exceeded the {NODE_CEILING}-node ceiling \
                     (visited {nodes})"
                )
            }
        }
    }
}

/// Successful-walk summary. Feeds the exactness manifest via
/// [`record_observations`] at the production chokepoints.
#[derive(Debug, Default, Clone)]
pub struct FragmentReport {
    pub assertions_checked: usize,
    /// Debug-names of every DeclKind seen ("EQ", "BAND", ...).
    pub observed_decl_kinds: BTreeSet<String>,
    /// Debug-names of every SortKind seen ("Bool", "Int", "BV").
    pub observed_sort_kinds: BTreeSet<String>,
}

/// Per-assertion sort flags for the theory-mix check.
#[derive(Debug, Default, Clone, Copy)]
struct AssertionScan {
    saw_int: bool,
    saw_bv: bool,
}

/// Walk every assertion in `solver.get_assertions()` and verify the
/// whole stack is inside the documented decidable fragment. Pure: no
/// global state, no recording. First violation wins, with a fixed check
/// order per node — (1) AstKind, (2) DeclKind allowlist + UNINTERPRETED
/// arity, (3) sort allowlist + BV width — then children are pushed; the
/// theory-mix check runs after each assertion's walk completes. Which
/// layer rejects a multi-violation formula is deliberately NOT a
/// contract (AG-Z1) — only that rejection is deterministic.
pub fn check_fragment(solver: &Solver<'_>) -> Result<FragmentReport, FragmentViolation> {
    let mut report = FragmentReport::default();
    let mut visited_total: usize = 0;

    for assertion in solver.get_assertions() {
        let root = Dynamic::from_ast(&assertion);
        let scan = walk_assertion(&root, &mut visited_total, &mut report)?;
        if let Some(v) = mix_violation(scan, &root) {
            return Err(v);
        }
        report.assertions_checked += 1;
    }

    Ok(report)
}

/// The DeclKind allowlist as data, for the exactness manifest: the
/// manifest asserts `observed ∪ {TRUE, FALSE}` == this set, so the
/// allowlist can't silently grow past what production queries use.
/// TRUE/FALSE are admitted (rejecting the constant `true` would be
/// absurd if Z3 ever surfaces it) but never observed — the manifest
/// pins them as the ONLY allowed-but-unobserved entries.
pub fn allowed_decl_kind_names() -> BTreeSet<String> {
    [
        // Shared propositional skeleton.
        "EQ",
        "NOT",
        // QF_LIA: refinements + fuel/split balance.
        "LE",
        "GE",
        "LT",
        "GT",
        "ANUM",
        // QF_BV<32>: authority masks.
        "BAND",
        "ULEQ",
        "BNUM",
        // Structural Bool constants (see above).
        "TRUE",
        "FALSE",
        // Free constants (arity-0 UNINTERPRETED).
        "UNINTERPRETED",
    ]
    .iter()
    .map(|s| (*s).to_string())
    .collect()
}

/// Iterative worklist walk of one assertion (ET-Z8: no recursion; the
/// shared `visited_total` enforces [`NODE_CEILING`] across the whole
/// call). The seen-set is per-assertion so the mix flags of THIS
/// assertion register every subterm even when assertions share DAG
/// nodes; within one assertion, shared nodes are visited once.
fn walk_assertion(
    root: &Dynamic<'_>,
    visited_total: &mut usize,
    report: &mut FragmentReport,
) -> Result<AssertionScan, FragmentViolation> {
    let mut scan = AssertionScan::default();
    let mut seen: HashSet<Dynamic<'_>> = HashSet::new();
    let mut worklist: Vec<Dynamic<'_>> = vec![root.clone()];

    while let Some(node) = worklist.pop() {
        if !seen.insert(node.clone()) {
            continue;
        }
        *visited_total += 1;
        if *visited_total > NODE_CEILING {
            return Err(FragmentViolation::TooLarge {
                nodes: *visited_total,
            });
        }

        // (1) AstKind: terms only. Var = a de Bruijn bound variable, which
        // only exists under a quantifier — either way, out of fragment.
        match node.kind() {
            AstKind::Numeral | AstKind::App => {}
            other => {
                return Err(FragmentViolation::DisallowedAstKind {
                    kind: format!("{other:?}"),
                    node: snippet(&node),
                });
            }
        }

        // (2) DeclKind allowlist. Numerals are decl-bearing in this
        // binding (`is_app` covers Numeral), so the walk is uniform; the
        // Err arm is unreachable after the kind gate but stays total.
        let decl = match node.safe_decl() {
            Ok(d) => d,
            Err(_) => {
                return Err(FragmentViolation::DisallowedAstKind {
                    kind: "non-application".to_string(),
                    node: snippet(&node),
                });
            }
        };
        let decl_kind = decl.kind();
        match decl_kind {
            DeclKind::EQ
            | DeclKind::NOT
            | DeclKind::LE
            | DeclKind::GE
            | DeclKind::LT
            | DeclKind::GT
            | DeclKind::ANUM
            | DeclKind::BAND
            | DeclKind::ULEQ
            | DeclKind::BNUM
            | DeclKind::TRUE
            | DeclKind::FALSE => {}
            DeclKind::UNINTERPRETED => {
                let arity = decl.arity();
                if arity > 0 {
                    return Err(FragmentViolation::UninterpretedFunction {
                        name: decl.name(),
                        arity,
                        node: snippet(&node),
                    });
                }
            }
            // Default-REJECT (deliberate `_`; see module docs §3): AND,
            // OR, ITE, ADD, MUL, BMUL, UGT, BV2INT, SELECT, DISTINCT, …
            // and every op a future z3 version adds.
            other => {
                return Err(FragmentViolation::DisallowedOp {
                    decl_kind: format!("{other:?}"),
                    decl_name: decl.name(),
                    node: snippet(&node),
                });
            }
        }
        report.observed_decl_kinds.insert(format!("{decl_kind:?}"));

        // (3) Sort allowlist: Bool, Int, BV of width exactly 32.
        let sort_kind = node.sort_kind();
        match sort_kind {
            SortKind::Bool => {}
            SortKind::Int => scan.saw_int = true,
            SortKind::BV => {
                let width = node.as_bv().map(|b| b.get_size()).unwrap_or(0);
                if width != 32 {
                    return Err(FragmentViolation::NonWidth32Bv {
                        width,
                        node: snippet(&node),
                    });
                }
                scan.saw_bv = true;
            }
            other => {
                return Err(FragmentViolation::DisallowedSort {
                    sort: format!("{other:?}"),
                    node: snippet(&node),
                });
            }
        }
        report.observed_sort_kinds.insert(format!("{sort_kind:?}"));

        worklist.extend(node.children());
    }

    Ok(scan)
}

/// The per-assertion theory-mix rule (inventory §4: authority bv32 and
/// fuel/refinement Int never share a constraint; the propositional
/// skeleton may be shared). The op allowlist already makes a mix
/// unreachable — no connective or conversion op is admitted — so this
/// is defense-in-depth in case the allowlist ever grows one.
fn mix_violation(scan: AssertionScan, root: &Dynamic<'_>) -> Option<FragmentViolation> {
    if scan.saw_int && scan.saw_bv {
        Some(FragmentViolation::MixedTheories {
            node: snippet(root),
        })
    } else {
        None
    }
}

/// Truncated rendering of the offending node. Materializes the full
/// string once on the error path only.
fn snippet(node: &Dynamic<'_>) -> String {
    let full = node.to_string();
    if full.chars().count() <= SNIPPET_MAX_CHARS {
        full
    } else {
        let mut s: String = full.chars().take(SNIPPET_MAX_CHARS).collect();
        s.push('…');
        s
    }
}

// ---------------------------------------------------------------------
// The observation accumulator (the exactness manifest's data source).
// Process-wide, like z3_cache::GLOBAL; fed ONLY by the production
// chokepoints so canaries never pollute the manifest (ET-Z7's
// lock+reset discipline lives in the manifest test itself).
// ---------------------------------------------------------------------

type ObservedSets = (BTreeSet<String>, BTreeSet<String>);

static OBSERVED: OnceLock<Mutex<ObservedSets>> = OnceLock::new();

fn observed() -> &'static Mutex<ObservedSets> {
    OBSERVED.get_or_init(|| Mutex::new((BTreeSet::new(), BTreeSet::new())))
}

/// Merge a successful walk's observations into the process-wide
/// accumulator. Called by the production chokepoints only — never by
/// [`check_fragment`] itself.
pub fn record_observations(report: &FragmentReport) {
    let mut sets = observed().lock().expect("observed-sets lock poisoned");
    sets.0.extend(report.observed_decl_kinds.iter().cloned());
    sets.1.extend(report.observed_sort_kinds.iter().cloned());
}

/// Snapshot `(decl_kinds, sort_kinds)` for the exactness manifest.
#[doc(hidden)]
pub fn observed_snapshot() -> ObservedSets {
    observed()
        .lock()
        .expect("observed-sets lock poisoned")
        .clone()
}

/// Reset the accumulator (the manifest test's reset-first discipline,
/// ET-Z7). The `OnceLock` stays initialized — only the sets clear.
#[doc(hidden)]
pub fn reset_observations_for_test() {
    let mut sets = observed().lock().expect("observed-sets lock poisoned");
    sets.0.clear();
    sets.1.clear();
}

#[cfg(test)]
mod tests {
    use super::*;
    use z3::ast::{BV, Bool, Int};
    use z3::{Config, Context};

    fn ctx() -> Context {
        Context::new(&Config::new())
    }

    /// The mix detector itself, on synthetic flags — it is unreachable
    /// through real walks (every combining op is rejected first), which
    /// is exactly why it gets a direct unit test (ET-Z5).
    #[test]
    fn mix_detector_fires_on_both_theories() {
        let c = ctx();
        let root = Dynamic::from_ast(&Bool::new_const(&c, "b"));
        let both = AssertionScan {
            saw_int: true,
            saw_bv: true,
        };
        assert!(matches!(
            mix_violation(both, &root),
            Some(FragmentViolation::MixedTheories { .. })
        ));
        for (saw_int, saw_bv) in [(true, false), (false, true), (false, false)] {
            assert!(mix_violation(AssertionScan { saw_int, saw_bv }, &root).is_none());
        }
    }

    /// The walk's sort flags register per assertion: an Int query sets
    /// saw_int only; a BV<32> query sets saw_bv only.
    #[test]
    fn walk_collects_per_assertion_sort_flags() {
        let c = ctx();
        let mut report = FragmentReport::default();
        let mut visited = 0usize;

        let x = Int::new_const(&c, "x");
        let int_root = Dynamic::from_ast(&x.gt(&Int::from_i64(&c, 5)));
        let scan = walk_assertion(&int_root, &mut visited, &mut report).expect("in-fragment");
        assert!(scan.saw_int && !scan.saw_bv);

        let b = BV::new_const(&c, "b", 32);
        let bv_root = Dynamic::from_ast(&b._eq(&BV::from_u64(&c, 3, 32)));
        let scan = walk_assertion(&bv_root, &mut visited, &mut report).expect("in-fragment");
        assert!(scan.saw_bv && !scan.saw_int);
    }

    /// Verdict purity: two walks of the same solver yield identical
    /// reports. (The companion property — `check_fragment` never touches
    /// the global accumulator — is NOT asserted here via a snapshot: the
    /// lib test binary runs `compiler::tests` in parallel threads whose
    /// real compiles record through the production chokepoints, so any
    /// global-emptiness assertion is racy by construction. The property
    /// holds structurally — `record_observations` is the only writer and
    /// `check_fragment` never calls it — and the exactness manifest in
    /// z3_corpus.rs verifies recording behavior in a binary where the
    /// recording population is fully known.)
    #[test]
    fn check_fragment_is_pure_and_deterministic() {
        let c = ctx();
        let solver = Solver::new(&c);
        let x = Int::new_const(&c, "x");
        solver.assert(&x.le(&Int::from_i64(&c, 7)));

        let a = check_fragment(&solver).expect("in-fragment");
        let b = check_fragment(&solver).expect("in-fragment");
        assert_eq!(a.observed_decl_kinds, b.observed_decl_kinds);
        assert_eq!(a.observed_sort_kinds, b.observed_sort_kinds);
        assert_eq!(a.assertions_checked, b.assertions_checked);
    }
}
