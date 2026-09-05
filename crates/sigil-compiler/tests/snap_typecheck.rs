//! Pillar 2 — golden snapshots of the **type-check pass** output.
//!
//! For every fixture in [`sigil_test_utils::snap_fixtures::FIXTURES`],
//! drive the snippet through parse → name-resolution → type-check
//! and snapshot the resulting [`TypedProgram`] with canonical span
//! filtering applied. A refactor that subtly changes how the type-
//! checker encodes a Type variant or attaches a refinement clause
//! surfaces here as a localized snapshot diff.
//!
//! ## Adding fixtures
//!
//! Add a tuple to `snap_fixtures::FIXTURES`. On the next test run,
//! `cargo insta test` will generate a pending snapshot; `cargo insta
//! review` lets you inspect + accept it.
//!
//! ## Reacting to failing snapshots
//!
//! 1. Run `cargo insta review` to see the diff.
//! 2. If the change is intentional and the new behavior is correct:
//!    accept the snapshot (`a` in review). Commit the updated
//!    `.snap` file alongside your code change.
//! 3. If the diff is unexpected: reject (`r`) and revert your change.

use sigil_test_utils::assert_canonical_snapshot;
use sigil_test_utils::pipeline::typecheck_or_panic;
use sigil_test_utils::snap_fixtures::FIXTURES;

/// Enabled by PR 5 (HashMap→BTreeMap swap for snapshot determinism).
/// Three production fields swapped to BTreeMap so this test's Debug
/// output is stable across runs:
///
///   * `EffectRegistry.effects` ([registries.rs:75]) — was
///     `HashMap<String, u32>`, now `BTreeMap<String, u32>`. Used
///     lookup-only in production; the iteration in `name_of(id)` is
///     filter-then-find-first (exactly one match), so order didn't
///     matter for correctness.
///   * `TypedProgram.records` and `.enums` ([typed_ast.rs:14-16]) —
///     were `HashMap<String, ...>`, now `BTreeMap<String, ...>`.
///     One-shot `.into_iter().collect()` at the drain site in
///     `check_with_options` (type_check/mod.rs); upstream
///     `universe.records` / `tracker.records` stay HashMap.
///
/// determinism_lock.rs (WASM byte-equality) verified unchanged
/// across the swap.
///
/// [registries.rs:75]: crates/sigil-compiler/src/registries.rs
/// [typed_ast.rs:14-16]: crates/sigil-compiler/src/typed_ast.rs
#[test]
fn snapshot_typecheck_pass() {
    for (name, src) in FIXTURES {
        let typed = typecheck_or_panic(src);
        assert_canonical_snapshot!(*name, &typed);
    }
}
