//! Pillar 2 — golden snapshots of the **WASM emission pass** output,
//! rendered as deterministic WAT text via `wasmprinter`.
//!
//! For every fixture in [`sigil_test_utils::snap_fixtures::FIXTURES`],
//! drive the snippet through the full compile pipeline and snapshot
//! the WAT-rendered form of `Compilation.wasm_inner`. Catches WASM-
//! emission regressions (changes to function bodies, locals layout,
//! imports/exports, custom sections) at the bytecode level.
//!
//! WAT is plain ASCII text with stable formatting, so the snapshots
//! diff cleanly in code review without needing the span-filter chain
//! that the TypedProgram and AirProgram snapshots use.
//!
//! ## determinism_lock.rs vs. snap_wat.rs
//!
//! The existing `tests/determinism_lock.rs` asserts WASM byte-equality
//! across consecutive runs and feature-flag toggles (an end-to-end
//! anti-regression). snap_wat.rs is COMPLEMENTARY: it pins the *shape*
//! of the emitted WAT for each fixture and surfaces shape changes as
//! reviewable diffs, where determinism_lock.rs would only tell you a
//! hash mismatched. Both are useful; both stay.
//!
//! See snap_typecheck.rs for the review workflow.

use sigil_test_utils::pipeline::compile_or_panic;
use sigil_test_utils::snap_fixtures::FIXTURES;
use sigil_test_utils::snapshot::wat_of;

#[test]
fn snapshot_wat_pass() {
    for (name, src) in FIXTURES {
        let comp = compile_or_panic(src);
        let wat = wat_of(&comp.wasm_inner);
        insta::assert_snapshot!(*name, wat);
    }
}
