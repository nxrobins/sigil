//! Shared snapshot-test fixtures — a small, hand-curated corpus of
//! SIGIL snippets exercising the type variants and language features
//! the type-check / AIR / WASM passes care most about.
//!
//! Each fixture is `(name, source)`. The `name` becomes the insta
//! snapshot name (`snap_typecheck__<name>.snap` etc.) — keep them
//! stable across PRs.
//!
//! The corpus is intentionally small and inline (rather than file-
//! backed) so the source travels with the snapshot in code review:
//! one diff window shows both the fixture and what the pass produced
//! for it.

/// Snapshot-corpus entry. Tuple-shaped for ergonomic iteration:
///
/// ```rust,ignore
/// for (name, src) in sigil_test_utils::snap_fixtures::FIXTURES {
///     let typed = sigil_test_utils::pipeline::typecheck_or_panic(src);
///     sigil_test_utils::assert_canonical_snapshot!(name, &typed);
/// }
/// ```
pub type Fixture = (&'static str, &'static str);

/// The canonical snapshot-fixture corpus.
///
/// Coverage matrix (per the Four-Pillar plan, PR 2 acceptance):
///
/// * one fixture per `Type` variant the compiler reaches in
///   well-formed code: machine ints (i64, i32, u64, u32, f64),
///   bool, str, unit, Array, Slice (via Ref), Ref, generics,
///   IntLit (via polymorphic literal)
/// * one parametric function
/// * one match arm with narrowing
/// * one cross-module call
///
/// 12 entries total. Adding a 13th means understanding what new
/// coverage it gives — don't pad just to round the number.
pub const FIXTURES: &[Fixture] = &[
    (
        // Smallest viable program: zero-arg fn returning a constant.
        // Anchors the snapshot infrastructure itself — if this one
        // ever changes, something fundamental moved.
        "minimal_return_i64",
        "module m;\n\
         pub fn answer() -> i64 {\n    \
             return 42;\n\
         }\n",
    ),
    (
        // bool return + literal.
        "bool_literal_return",
        "module m;\n\
         pub fn always_true() -> bool {\n    \
             return true;\n\
         }\n",
    ),
    (
        // Each machine-integer variant exercised once. Catches
        // accidental changes to Type::I32/U32/I64/U64/F64 encoding in
        // either typed_ast or AIR lowering.
        "all_machine_integer_types",
        "module m;\n\
         pub fn i32_param(x: i32) -> i32 { return x; }\n\
         pub fn u32_param(x: u32) -> u32 { return x; }\n\
         pub fn i64_param(x: i64) -> i64 { return x; }\n\
         pub fn u64_param(x: u64) -> u64 { return x; }\n\
         pub fn f64_param(x: f64) -> f64 { return x; }\n",
    ),
    (
        // Unit return type (no explicit return type annotation).
        "unit_return_implicit",
        "module m;\npub fn nothing() {}\n",
    ),
    (
        // String literal + str type. str = UTF-8-validated bytes per
        // PR S1; the literal exercises Type::Str through lowering.
        "str_literal_constant",
        "module m;\n\
         pub fn greet() -> str {\n    \
             return \"hello\";\n\
         }\n",
    ),
    (
        // Fixed-size array. Exercises Type::Array { elem, size }
        // through both type-check (refinement attachment for length)
        // and AIR (record-style layout).
        "fixed_array_construct_and_index",
        "module m;\n\
         pub fn third(a: [i64; 5]) -> i64 {\n    \
             return a[2];\n\
         }\n",
    ),
    (
        // Sound `trap()` divergence (Tier A): the block ends in a `Never`-typed
        // `trap()`, so it lowers to a terminating `AirTerminator::Unreachable` —
        // NOT a fall-through `Return(None)`, which would be invalid wasm for this
        // non-unit (`i64`) return type. Locks the divergence lowering.
        "trap_diverges_terminates_block",
        "module m;\n\
         pub fn always_abort() -> i64 {\n    \
             trap();\n\
         }\n",
    ),
    (
        // Generic parametric function. Exercises Type::Generic +
        // monomorph cache + impl-method substitution. (Note: a
        // dedicated `&T` reference fixture is intentionally absent;
        // surface-level borrow syntax in SIGIL goes through ActorRef
        // or the slice form rather than the bare `&T` used in Rust.
        // Add a slice fixture in a follow-up if the slice-lowering
        // code grows.)
        "parametric_identity",
        "module m;\n\
         pub fn identity<T>(x: T) -> T {\n    \
             return x;\n\
         }\n\
         pub fn pin_i64() -> i64 {\n    \
             return identity::<i64>(42);\n\
         }\n",
    ),
    (
        // Polymorphic integer literal (PIL): `42` unifies with any
        // machine-int type at the binding site. Type::IntLit until
        // resolved.
        "polymorphic_int_literal_at_binding",
        "module m;\n\
         pub fn pinned() -> u32 {\n    \
             let x: u32 = 42;\n    \
             return x;\n\
         }\n",
    ),
    (
        // Match arm with literal-pattern narrowing — exercises the
        // Wall 4 Step 6/10 narrowing pipeline that produces
        // `pattern_refinement_stack` entries. SIGIL match arms
        // require a trailing comma after each block-bodied arm.
        "match_arm_literal_narrowing",
        "module m;\n\
         pub fn classify(x: i64) -> i64 {\n    \
             match x {\n        \
                 0 => { return 100; },\n        \
                 1 => { return 200; },\n        \
                 _ => { return 0; },\n    \
             }\n\
         }\n",
    ),
    (
        // Record type with named fields. Exercises TypeUniverse.records
        // + AIR record layout + WASM struct-style memory access.
        "record_with_two_fields",
        "module m;\n\
         pub record Point { x: i64, y: i64 }\n\
         pub fn make_origin() -> Point {\n    \
             return Point { x: 0, y: 0 };\n\
         }\n",
    ),
    (
        // Enum with two variants, one payload-bearing.
        // Exercises TypeUniverse.enums + AIR tagged-union layout.
        "enum_with_payload_variant",
        "module m;\n\
         pub enum Maybe { None, Some(i64) }\n\
         pub fn wrap(x: i64) -> Maybe {\n    \
             return Maybe::Some(x);\n\
         }\n",
    ),
    (
        // DEF-2a lexical region: a memory scope whose allocations are reclaimed at
        // block exit. Exercises the AIR `RegionBegin`/`RegionEnd` nodes and the PR-5
        // WASM reclamation codegen — the BUMP_PTR (global 0) save/restore emitted in
        // module-level bodies (`GlobalGet 0; LocalSet save` … `LocalGet save; GlobalSet
        // 0`). The FIRST fixture to use `region`, so it anchors the region WAT golden.
        "region_reclaim",
        "module m;\n\
         pub fn run() -> i64 ! { Alloc } {\n    \
             region scratch(64) {\n        \
                 let inner: i64 = 42;\n        \
                 let _used: i64 = inner + 1;\n    \
             };\n    \
             return 1;\n\
         }\n",
    ),
    (
        // RANGE-FOR (RF-M0): the exclusive i64 range loop, WITH an `arr[i]` body
        // index. Anchors (a) the ForRange AIR shape — the hoisted `__r_end`
        // pre-header, the I64 `v < __r_end` cond + `Loop` terminator, the I64
        // increment block — and (b) the M0 memory-safety FLOOR: the body index's
        // full runtime bounds chain (`LoadField(len)` / `WrapI64` / `oob` /
        // `TrapIf`) is PRESENT (nothing elided). RF-M2's elision will change this
        // golden deliberately (the chain vanishes) — the diff IS the feature.
        "range_for_basic",
        "module m;\n\
         pub fn sum3(a: [i64; 3]) -> i64 {\n    \
             let mut acc = 0;\n    \
             for i in 0..3 {\n        \
                 acc = acc + a[i];\n    \
             }\n    \
             return acc;\n\
         }\n",
    ),
];
