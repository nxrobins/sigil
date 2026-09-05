//! Duplicate-name census — the fence for the fail-open duplicate-name class.
//!
//! SIGIL's duplicate-name validation is per-declaration-namespace, and each
//! namespace was historically checked (or NOT) by its own bespoke pass. The
//! ones nobody wrote a pass for compiled **fail-open**: a duplicate silently
//! shadowed or collided (record fields were the flagship case, closed by
//! N013 #424; the same "a per-case pass forgot a case" family as the
//! Type-walker Fn/Tuple-arm bugs fenced by walker_fence.rs / PR #558).
//!
//! This test is a COMPLETE accounting of every declarable member-name
//! namespace. Each is either:
//!   - `Rejects(code)` — a duplicate fires that exact diagnostic, OR
//!   - `KnownGap`      — still fail-open, compiles clean, tracked here.
//!
//! Two fences:
//!   1. Every `Rejects` namespace is pinned to its code (regression fence:
//!      a fix silently regressing to fail-open turns the row red).
//!   2. Every `KnownGap` namespace is asserted to STILL compile clean — so
//!      when a future iteration closes it, THIS test goes red and forces the
//!      row to be flipped to `Rejects(code)`. The gap can never be quietly
//!      "fixed and forgotten" nor quietly regress.
//!
//! The compile-time half of the fence lives in `name_resolution.rs`: the
//! census `match item` is TOTAL over `Item`, so a new declaration kind fails
//! to compile until its member-name namespaces are classified.

use sigil_compiler::compile_named_module;
use std::collections::BTreeSet;

#[derive(Clone, Copy)]
enum Expect {
    /// A duplicate in this namespace must fire this exact code.
    Rejects(&'static str),
    /// Still fail-open. Compiles clean today; tracked for a future slice.
    /// The `&str` is the reason / what's needed to close it.
    KnownGap(&'static str),
}
use Expect::*;

fn emitted_codes(src: &str) -> Vec<String> {
    match compile_named_module("dup_census.sigil", src.to_owned()) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut cs: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            cs.sort();
            cs.dedup();
            cs
        }
    }
}

/// (namespace label, source with a duplicate member name, expectation).
/// Adding a declarable member-name namespace? Add a row here — the
/// `name_resolution.rs` census match is total, so the compiler already
/// forced you to consider it there.
const CENSUS: &[(&str, &str, Expect)] = &[
    // ── Covered (regression-fenced) ──────────────────────────────────────
    (
        "top-level item names",
        "module m;\nfn f() -> i64 { return 1; }\nfn f() -> i64 { return 2; }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N002"),
    ),
    (
        "cross-kind top-level names",
        "module m;\nrecord X { a: i64 }\nfn X() -> i64 { return 1; }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N002"),
    ),
    (
        "module names",
        "module m;\nfn f() -> i64 { return 1; }\nmodule m;\nfn g() -> i64 { return 2; }\n",
        Rejects("N001"),
    ),
    (
        "function params",
        "module m;\nfn f(a: i64, a: i64) -> i64 { return a; }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N005"),
    ),
    (
        "actor state fields",
        "module m;\nentry actor Main {\n  state { x: i64, x: i64 }\n  on Start() -> i64 { return 1; }\n}\n",
        Rejects("N004"),
    ),
    (
        "actor handlers",
        "module m;\nentry actor Main {\n  on Start() -> i64 { return 1; }\n  on Start() -> i64 { return 2; }\n}\n",
        Rejects("N003"),
    ),
    (
        "actor handler params",
        "module m;\nentry actor Main {\n  on Start() -> i64 { return 1; }\n  on Go(a: i64, a: i64) -> i64 { return a; }\n}\n",
        Rejects("N005"),
    ),
    (
        "record fields",
        "module m;\nrecord R { a: i64, a: i64 }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N013"),
    ),
    (
        "enum variants",
        "module m;\nenum E { A, A }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N014"),
    ),
    (
        "cap authorities",
        "module m;\ncap type Fuel { burn, burn }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N015"),
    ),
    (
        "protocol states",
        "module m;\nrecord File { x: i64 }\nstate File { Open, Open }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N016"),
    ),
    (
        "fn type params",
        "module m;\nfn f<T, T>(x: T) -> i64 { return 1; }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N017"),
    ),
    (
        "record type params",
        "module m;\nrecord Box<T, T> { v: T }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N017"),
    ),
    (
        "enum type params",
        "module m;\nenum Box<T, T> { V(T) }\nfn boot() -> i64 { return 0; }\n",
        Rejects("N017"),
    ),
    (
        "enum named-payload fields",
        "module m;\nenum E { V(a: i64, a: i64) }\nfn boot() -> i64 { return 0; }\n",
        Rejects("T223"),
    ),
    (
        "impl type params",
        "module m;\nrecord Box<T> { v: T }\nimpl Box<T, T> {\n  fn get(self: Box<T>) -> i64 { return 1; }\n}\nfn boot() -> i64 { return 0; }\n",
        Rejects("T229"),
    ),
    (
        "actor init params",
        "module m;\nentry actor Main {\n  state { x: i64 }\n  init(a: i64, a: i64) { x = a; }\n  on Start() -> i64 { return 1; }\n}\n",
        Rejects("N005"),
    ),
    // The param family: N005 rode only the free-fn + actor init/handler paths;
    // every other param-bearing decl was fail-open until the same helper was
    // wired to it. An impl method is live, running code — a duplicate param
    // silently bound one of the two.
    (
        "impl method params",
        "module m;\nrecord R { a: i64 }\nimpl R {\n  fn m(self: R, b: i64, b: i64) -> i64 { return b; }\n}\nfn boot() -> i64 { return 0; }\n",
        Rejects("N005"),
    ),
    (
        "effect operation params",
        "module m;\neffect R {\n  fn put(a: i64, a: i64) -> i64;\n}\nfn boot() -> i64 { return 0; }\n",
        Rejects("N005"),
    ),
    (
        "trait method params",
        "module m;\ntrait T {\n  fn m(self: Self, b: i64, b: i64) -> i64;\n}\nfn boot() -> i64 { return 0; }\n",
        Rejects("N005"),
    ),
    (
        "extern fn params",
        // The grammar rejects the duplicate before name-resolution ever sees
        // it; pinned so a parser change can't silently open the hole.
        "module m;\n#[ring(outer)] #[trusted]\nextern \"C\" fn ext(a: i64, a: i64) -> i64 ! { FFI, Unsafe }\nfn boot() -> i64 { return 0; }\n",
        Rejects("P002"),
    ),
    // ── Known gaps (tracked; each will flip to Rejects when a slice lands) ─
    // Closed by the formal gate rather than by a dedicated name-resolution
    // pass: both duplicate methods lower to functions with the same root
    // export name, and the CSIR v9 declaration envelope refuses a root table
    // with duplicate names ("invalid occurrence declaration envelope:
    // RootContract", surfaced as I013 at the module span). The duplicate can
    // no longer compile fail-open; a source-level diagnostic with a precise
    // span would still be an improvement (dispatch/coherence-aware dedup).
    (
        "duplicate methods in one impl block",
        "module m;\nrecord R { a: i64 }\nimpl R {\n  fn m(self: R) -> i64 { return 1; }\n  fn m(self: R) -> i64 { return 2; }\n}\nfn boot() -> i64 { return 0; }\n",
        Rejects("I013"),
    ),
    (
        "duplicate methods across impl blocks",
        "module m;\nrecord R { a: i64 }\nimpl R {\n  fn m(self: R) -> i64 { return 1; }\n}\nimpl R {\n  fn m(self: R) -> i64 { return 2; }\n}\nfn boot() -> i64 { return 0; }\n",
        Rejects("I013"),
    ),
    (
        "duplicate effect operations",
        "module m;\neffect R {\n  fn get() -> i64;\n  fn get() -> i64;\n}\nfn boot() -> i64 { return 0; }\n",
        KnownGap("effect-op dedup: fold into the census once EH lands its op table"),
    ),
    (
        "duplicate trait methods",
        "module m;\ntrait T {\n  fn m(self: Self) -> i64;\n  fn m(self: Self) -> i64;\n}\nfn boot() -> i64 { return 0; }\n",
        KnownGap("trait-method dedup: separate slice"),
    ),
    // In-pattern binders. Rust makes these a hard error (E0416); SIGIL accepts
    // them today and one binder silently wins. Left as a gap deliberately:
    // unlike a decl's member list, a pattern binder's rule is a SEMANTIC choice
    // (reject vs. shadow) that should be decided once, for all pattern
    // positions, rather than smuggled in as a side effect of this census.
    (
        "let-tuple destructure binders",
        "module m;\nfn boot() -> i64 { let (a, a) = (1, 2); return a; }\n",
        KnownGap("pattern-binder policy (reject vs shadow) undecided; see also match arms"),
    ),
    (
        "match arm payload binders",
        "module m;\nenum P { V(i64, i64) }\nfn boot() -> i64 {\n  let p: P = P::V(1, 2);\n  match p { P::V(x, x) => { return x; } }\n}\n",
        KnownGap("pattern-binder policy (reject vs shadow) undecided; see also let-tuple"),
    ),
];

#[test]
fn duplicate_name_census_is_complete_and_pinned() {
    const CENSUS_CASE_FLOOR: usize = 27;
    let labels: BTreeSet<&str> = CENSUS.iter().map(|(label, _, _)| *label).collect();
    assert_eq!(labels.len(), CENSUS.len(), "duplicate census case label");
    assert!(
        labels.len() >= CENSUS_CASE_FLOOR,
        "duplicate-name census fell to {} cases (floor {CENSUS_CASE_FLOOR})",
        labels.len()
    );

    let mut failures = Vec::new();
    for (label, src, expect) in CENSUS {
        let codes = emitted_codes(src);
        match expect {
            Rejects(code) => {
                if !codes.iter().any(|c| c == code) {
                    failures.push(format!(
                        "[{label}] expected duplicate to REJECT with {code}, got {codes:?} — \
                         a covered namespace regressed to fail-open"
                    ));
                }
            }
            KnownGap(reason) => {
                if !codes.is_empty() {
                    failures.push(format!(
                        "[{label}] now emits {codes:?} but is marked KnownGap ({reason}) — \
                         if you CLOSED this gap, flip its census row to Rejects(<code>); \
                         if this is an unrelated error, adjust the fixture"
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "duplicate-name census:\n{}",
        failures.join("\n")
    );
}

/// Focused soundness fixtures for the two security-relevant closures, kept
/// separate so their intent is legible (red→green anchors for N014/N015).
#[test]
fn enum_variant_duplicate_is_rejected_not_silently_tag_collided() {
    // Source-order tag assignment means a duplicate `A` would take tags 0 AND
    // 1; construction and matching would silently resolve to the first,
    // leaving the second unreachable. Must reject.
    assert!(
        emitted_codes("module m;\nenum Dir { N, S, N }\nfn boot() -> i64 { return 0; }\n")
            .iter()
            .any(|c| c == "N014")
    );
}

#[test]
fn cap_authority_duplicate_is_rejected_not_silently_bit_inflated() {
    // A duplicate authority inflates the mask's authority count (wasting the
    // 32-authority T185 budget) and is unreachable via `restrict` (the mask
    // lookup returns the first bit). Must reject.
    assert!(
        emitted_codes(
            "module m;\ncap type W { read, write, read }\nfn boot() -> i64 { return 0; }\n"
        )
        .iter()
        .any(|c| c == "N015")
    );
}

#[test]
fn non_duplicate_declarations_stay_clean() {
    // No false positives: distinct member names in every fenced namespace.
    for src in [
        "module m;\nenum E { A, B, C }\nfn boot() -> i64 { return 0; }\n",
        "module m;\ncap type W { read, write }\nfn boot() -> i64 { return 0; }\n",
        "module m;\nrecord File { x: i64 }\nstate File { Open, Closed }\nfn boot() -> i64 { return 0; }\n",
        "module m;\nfn f<T, U>(x: T, y: U) -> i64 { return 1; }\nfn boot() -> i64 { return 0; }\n",
        "module m;\nrecord Box<T, U> { a: T, b: U }\nfn boot() -> i64 { return 0; }\n",
    ] {
        let codes = emitted_codes(src);
        assert!(
            codes.is_empty(),
            "expected clean compile, got {codes:?} for `{src}`"
        );
    }
}
