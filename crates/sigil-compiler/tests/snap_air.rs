//! Pillar 2 — golden snapshots of the **AIR lowering pass** output.
//!
//! For every fixture in [`sigil_test_utils::snap_fixtures::FIXTURES`],
//! drive the snippet through the full compile pipeline and snapshot
//! the resulting [`AirProgram`] with canonical span filtering applied.
//! Catches "did the IR encoding of capabilities / records / effects
//! change?" regressions that wouldn't be obvious in either the type-
//! check snapshot or the WAT snapshot.
//!
//! The snapshotted AIR is the **post-memory-lowering, post-fuel-insertion**
//! form — i.e., what `wasm::emit` consumes. That's the right cut for
//! catching regressions that affect the WASM bytes downstream.
//!
//! See snap_typecheck.rs for the review workflow.

use sigil_test_utils::assert_canonical_snapshot;
use sigil_test_utils::pipeline::compile_or_panic;
use sigil_test_utils::snap_fixtures::FIXTURES;

/// Enabled by PR 5 (HashMap→BTreeMap swap for snapshot determinism).
/// `AirFunction.value_kinds` and `.debug_names` ([air.rs:31-32]) and
/// the matching `FunctionLowerer` / `LoweredFunctionBody` fields are
/// now `BTreeMap`. Codegen never iterates these maps — only
/// `.get(&var)` lookups (`var_kind`, `var_label`) — so WASM byte-
/// equality is preserved per determinism_lock.rs.
///
/// `VarId` gained `Ord + PartialOrd` derives so it can be a BTreeMap
/// key. Required because deriving `Ord` is the standard contract for
/// keyed lookup in a sorted-map structure.
///
/// [air.rs:31-32]: crates/sigil-compiler/src/air.rs
#[test]
fn snapshot_air_pass() {
    for (name, src) in FIXTURES {
        let comp = compile_or_panic(src);
        assert_canonical_snapshot!(*name, &comp.air);
    }
}
