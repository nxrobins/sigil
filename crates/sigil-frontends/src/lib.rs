//! `sigil-frontends` — untrusted source-to-source translators that compile an
//! external surface DSL into SIGIL **text**, then hand it to the mature Rust
//! `sigil-compiler` for verification. The frontend is an *untrusted translator*;
//! SIGIL is the **trust anchor**. See `docs/specs/foreign-frontends.md`.
//!
//! Design invariant (the spine, threat T15): the compiler only ever checks the
//! *emitted* text against itself — it never sees the authored DSL — so the
//! translator itself MUST guarantee that the emitted authority envelope equals
//! the authored policy, and MUST fail-fast (emit nothing) on anything it does
//! not fully recognize. Every bound here is a "dumb" physical limit; see the
//! Constraints & Fallbacks matrix in the spec.

#![forbid(unsafe_code)]

pub mod rust;
pub mod solidity;
pub mod typescript;

// SOL-XFILE: the Solidity-only multi-file project entry (the shared `Frontend` trait
// stays single-file — TS/Rust are untouched). See `solidity/project.rs`.
pub use solidity::project::translate_solidity_project;

use std::ops::Range;

/// A byte range in the foreign (source-DSL) text.
pub type ForeignSpan = Range<usize>;

/// FE-prefixed translator-level diagnostic codes. These name *translator*
/// rejections; errors in the emitted SIGIL still surface as the compiler's own
/// `T-`/`E-` codes. `FE012`/`FE500` are internal-invariant codes — if they fire
/// it means the translator itself is buggy, never a user-policy fault.
pub mod codes {
    /// Construct outside the supported subset (incl. deferred `@effects`).
    pub const FE001_UNSUPPORTED: &str = "FE001";
    /// Input/complexity bound exceeded (size, depth, function count).
    pub const FE002_TOO_LARGE: &str = "FE002";
    /// Unrecognized/misspelled policy annotation (fail-closed; threat T1).
    pub const FE010_UNKNOWN_ANNOTATION: &str = "FE010";
    /// `@cap`-derived cap parameter never threaded into the body (threat T2).
    pub const FE011_DECORATIVE_CAP: &str = "FE011";
    /// Emitted authority envelope ≠ authored policy (internal; threat T15).
    pub const FE012_AUTHORITY_MISMATCH: &str = "FE012";
    /// Identifier outside `^[A-Za-z_][A-Za-z0-9_]{0,63}$` (threat T7).
    pub const FE020_BAD_IDENTIFIER: &str = "FE020";
    /// Identifier collides with a SIGIL keyword or the `__fe_` prefix (T8).
    pub const FE021_RESERVED_NAME: &str = "FE021";
    /// Numeric literal not an exact in-range decimal i64 (threat T9).
    pub const FE030_BAD_NUMBER: &str = "FE030";
    /// Operator outside the FE0 whitelist (threat T16).
    pub const FE031_BAD_OPERATOR: &str = "FE031";
    /// A `@cap`-bearing function is called intra-program (anti-goal T13).
    pub const FE040_CAP_CALLEE: &str = "FE040";
    /// Emitted SIGIL failed the parse self-check (internal; threat T10).
    pub const FE500_INTERNAL_MALFORMED: &str = "FE500";

    // ── FE1 (effect contracts) ──────────────────────────────────────────────
    /// A file mixes `@cap` and `@effects` (mode is per-file homogeneous; F1).
    pub const FE201_MIXED_MODE: &str = "FE201";
    /// A `@cap` item reached effect-mode emission (internal backstop; F6).
    pub const FE202_CAP_IN_EFFECT_MODE: &str = "FE202";
    /// An emitted effect row references a name with no co-emitted `effect` decl
    /// (internal; the compiler would silently drop it — F5, the FE1 spine).
    pub const FE210_EFFECT_UNDECLARED: &str = "FE210";
    /// An emitted top-level name collides with another (effect/cap-type vs fn);
    /// the collision is N002 at name-resolution, invisible to FE500 (F7).
    pub const FE211_NAME_COLLISION: &str = "FE211";
    /// An author `@effects` name collides with a compiler-reserved effect (F11).
    pub const FE213_RESERVED_EFFECT: &str = "FE213";
    /// Marker for the determinism (two-run byte-compare) test (F4).
    pub const FE502_NONDETERMINISTIC: &str = "FE502";

    // ── FE2 (broadened subset: booleans, records, control flow) ─────────────
    /// An in-subset TS expression/statement is ill-typed (H2 spine); the
    /// translator's own sound checker rejects rather than emit a T-code.
    pub const FE301_ILL_TYPED: &str = "FE301";
    /// A record construction omits a declared field (H1; compiler accepts it
    /// silently, so the translator must enforce all-fields-present).
    pub const FE302_MISSING_FIELD: &str = "FE302";
    /// An `if`/`while` condition is not statically `bool` (H4; no truthiness).
    pub const FE303_TRUTHY_CONDITION: &str = "FE303";
    /// An object literal whose expected record type is not statically
    /// inferable (H13; SIGIL has no anonymous/structural record literal).
    pub const FE304_UNTYPED_OBJECT_LITERAL: &str = "FE304";
    /// A record construction supplies an unknown/extra field (H1).
    pub const FE305_UNKNOWN_FIELD: &str = "FE305";
    /// A non-unit function has a control-flow path that does not `return` (H5).
    pub const FE306_NON_EXHAUSTIVE_RETURN: &str = "FE306";
    /// A reassignment that cannot lower to a legal `let mut` rebinding (H6).
    pub const FE307_ILLEGAL_REASSIGNMENT: &str = "FE307";
    /// A variable reference resolves to no in-scope binding (H7).
    pub const FE308_UNRESOLVED_REFERENCE: &str = "FE308";
    /// Unary `!` applied to a non-bool operand (H16).
    pub const FE309_NON_BOOL_NEGATION: &str = "FE309";
    /// A cross-interface use relying on TS structural (not nominal) typing (H17).
    pub const FE310_STRUCTURAL_MISMATCH: &str = "FE310";
    /// Relational `< <= > >=` on non-i64, or `==`/`!=` on unequal types (M7).
    pub const FE311_OPERAND_TYPE: &str = "FE311";
    /// A TS feature outside the FE2 subset (optional fields, methods, index
    /// sigs, extends, unions, interface generics, `/`/`%`, …) — fail-closed (H20).
    pub const FE320_UNSUPPORTED_TS: &str = "FE320";

    // ── FE4 (Solidity → SIGIL, SOL0) ────────────────────────────────────────
    // The frontend's existential risk is a translation that COMPILES (passes the
    // trusted re-verification) but MEANS something different from the source. Every
    // FE4 code is a fail-closed REJECT (emit nothing), never a best-effort/partial.
    /// A Solidity construct outside the SOL0 lowering table (inheritance, external
    /// calls, dynamic dispatch, modifiers, events, assembly, …) — fail-closed (NC-S6).
    pub const FE401_UNSUPPORTED_SOL: &str = "FE401";
    /// Input/complexity bound exceeded (size, nesting depth, function count).
    pub const FE402_TOO_LARGE_SOL: &str = "FE402";
    /// A declared type outside the SOL allow-set `{uint8..uint256 (×8), bool, address,
    /// bytes32, struct, enum}` — signed `int*`, non-multiple-of-8 / >256 widths,
    /// `bytesN` for N<32 (LEFT-aligned in Solidity; a right-aligned u256 carrier would
    /// mis-compare them — only full-width `bytes32` is unambiguous, SOL-ACCESS EX-3),
    /// `string`/`bytes`, and unsupported address/global members — fail-closed (NC-S2/NC-S5).
    pub const FE410_UNSUPPORTED_TYPE: &str = "FE410";
    /// An `unchecked { }` block, or a `pragma solidity` whose admitted range is not
    /// wholly `>= 0.8.0` (pre-0.8 wraps; checked-only is the only faithful target) (NC-S3).
    pub const FE411_UNCHECKED_OR_PRAGMA: &str = "FE411";
    /// Non-checks-then-effects: a storage write can be followed by a trap-capable
    /// operation (`require`/`revert`/`assert` OR checked `+ - * / %`), which SIGIL's
    /// trap (no atomic rollback) cannot faithfully model (NC-S1).
    pub const FE412_NON_CEI: &str = "FE412";
    /// A state field whose initial value is not a single static value (no inline
    /// initializer, not unconditionally constructor-assigned) — zero-default cannot
    /// be safely guessed (NC-S4).
    pub const FE413_INDETERMINATE_INIT: &str = "FE413";
    /// An unrecognized/ambiguous guard form (`require`/`assert`/`revert`) the SOL0
    /// guard recognizer cannot model — never let it fall through as a no-op (NC AG-S4).
    pub const FE414_BAD_GUARD: &str = "FE414";
    /// A `mapping` nested DEEPER than the supported 2 levels (`mapping(a => mapping(b
    /// => mapping(c => v)))`, a 3-level write `m[a][b][c] = v`, or a mapping-typed key)
    /// — a faithful unbounded N-dimensional store has no bounded analog (AG-L3) (NC-L1).
    /// NOTE: two-level `mapping(a => mapping(b => v))` (the ERC20 `allowance`) IS
    /// supported as of SOL-ERC20 — a bounded two-key map (`BoundedMap2_u256_u256_u256_64`).
    pub const FE440_NESTED_MAPPING_SOL: &str = "FE440";
    /// A `mapping` key or value type outside the SOL1 map allow-set `{address,
    /// uint256, uint}` (e.g. a `bool`-keyed/valued map) — deferred, fail-closed (NC-L1).
    pub const FE441_BAD_MAP_KV_SOL: &str = "FE441";
    /// An index `[]` applied to a non-mapping, OR a `m[k]` whose key's static type does
    /// not EXACTLY match the mapping's declared key type (NC-L3d / LM6).
    pub const FE442_BAD_INDEX_SOL: &str = "FE442";
    /// A disallowed operation on an `address` value: arithmetic (`+ - * / %`),
    /// relational ordering (`< <= > >=`), or a silent `address`↔`uint256` mix
    /// (assign/compare/index-key) — `address` is a CLOSED distinct type (NC-L3a/b / LM3/LM4).
    /// Fires ONLY when an `address` is genuinely misused as/with a `uint256`; a pure
    /// type-kind mismatch that involves no `address` is FE445 instead.
    pub const FE443_ADDRESS_OP_SOL: &str = "FE443";
    /// An incompatible value/target type mismatch that does NOT involve an
    /// `address`↔`uint256` confusion (e.g. a `bool` flowing into a numeric slot, or a
    /// numeric literal into a `bool`) — in an assignment, return, comparison, index, or
    /// a state-field initializer. Kept distinct from FE443 so the address-misuse code
    /// stays precise (a consumer keying on FE443 means "address misuse", not "any type
    /// error").
    pub const FE445_TYPE_MISMATCH_SOL: &str = "FE445";
    /// A `view`/`pure` function performs a state write (a Solidity state-mutability
    /// violation — solc rejects it). The frontend rejects it early with a precise code
    /// rather than emitting a non-`@Mut` `self` method that only the trusted compiler's
    /// `@ReadOnly` check catches downstream.
    pub const FE446_VIEW_WRITE_SOL: &str = "FE446";

    // ── FE4 (Solidity → SIGIL, SOL1c: modifiers → inlined guards) ───────────
    // A modifier is INLINED around the function body (`_` = the body) in the desugar
    // pass; check/emit see the merged body. Every code below is a fail-closed reject:
    // the existential failure for a security translator is a modifier that COMPILES but
    // drops its guard, so an un-inlined / mis-spliced modifier is FE500 (E1), never best-effort.
    /// A `modifier` body does not contain EXACTLY ONE `_` placeholder (0 would silently
    /// drop the function body; >1 would duplicate it — deferred). Counted across nested
    /// `if` branches (AG-MOD-2).
    pub const FE447_MODIFIER_PLACEHOLDER_SOL: &str = "FE447";
    /// A parameterized modifier — declared with params, or applied with an argument list
    /// (`f() onlyAfter(t)`). Argument substitution is the name-capture bug class; SOL1c
    /// supports parameterless modifiers only (AG-MOD-4).
    pub const FE448_PARAMETERIZED_MODIFIER_SOL: &str = "FE448";
    /// A modifier-introduced local-variable name collides with a host function
    /// local/param, **a contract state field**, or another applied modifier's local.
    /// Flat inlining merges the scopes, so the modifier local would silently shadow the
    /// colliding name — redirecting the host body's reads/writes of a state field to a
    /// dead local (a verified-but-wrong translation). Rejected, never alpha-renamed (AG-MOD-5).
    pub const FE449_MODIFIER_LOCAL_COLLISION_SOL: &str = "FE449";
    /// Two `modifier` declarations share a name — ambiguous which body to inline.
    pub const FE450_DUPLICATE_MODIFIER_SOL: &str = "FE450";
    /// A function applies a modifier name with no matching `modifier` declaration — never
    /// silently drop the guard.
    pub const FE451_UNDEFINED_MODIFIER_SOL: &str = "FE451";
    /// An unsupported function attribute in modifier position (`payable`/`virtual`/
    /// `override`) — they lex as bare idents; recognized as a fixed set and rejected
    /// precisely rather than reported as a confusing "undefined modifier" (AG-MOD-4).
    pub const FE452_UNSUPPORTED_ATTRIBUTE_SOL: &str = "FE452";
    /// A `modifier` has statements AFTER its `_` placeholder (a "suffix"). In Solidity
    /// such code runs on function EXIT — even after a body `return` — which a flat inline
    /// cannot model: when the host body returns, the suffix becomes dead code (e.g. a
    /// `nonReentrant` unlock that never runs, bricking the lock). The `_` must be in tail
    /// position; a suffix is rejected (AG-MOD-10).
    pub const FE453_MODIFIER_SUFFIX_SOL: &str = "FE453";

    // ── FE4 (Solidity → SIGIL, SOL-CAP v1: onlyOwner → unforgeable `&Cap` gate) ──
    // OPT-IN (`// sigil:cap-access-control`): translate the `onlyOwner` access-control
    // pattern into a `&C_Owner` capability gate instead of the forgeable `__fe_sender ==
    // owner` trap. The existential risk is a translation that compiles but is WEAKER than
    // the source; every code below is a fail-closed reject. See
    // docs/specs/solidity-access-control-via-capabilities.md (§7 E-1..E-6, §IMPL-1..5).
    /// cap-mode: the access-controlling address field `<F>` is used somewhere OTHER than
    /// the `onlyOwner` gate comparison (a getter return, another comparison, arithmetic, a
    /// map key, a second assignment, any read-as-data) IN THE SURVIVING program. The capability
    /// model only covers an address used PURELY as an authorization gate; a data use diverges
    /// observably, so it is rejected rather than silently cap-translated (E-2 / IMPL-1).
    /// SOL-HARDEN carve-out: a use inside a DISCARDED `event`/`emit` argument is EXEMPT — events
    /// have no SIGIL sink (SOL-EVENTS) and FE481 keeps a discarded arg side-effect-free, so a
    /// discarded owner read is sink-less. See the cap spec §E-2 + `compile/cap_emit_owner.sol`.
    pub const FE454_ADDRESS_USED_AS_DATA_SOL: &str = "FE454";
    /// cap-mode: a modifier is a near-miss of the exact `onlyOwner` gate shape
    /// (`require(msg.sender == <addr field>); _;`) — e.g. an extra statement, a compound
    /// condition, or a non-address operand. Rejected loudly rather than silently emitting
    /// the forgeable address model the user opted out of (E-1).
    pub const FE455_CAP_NEAR_MISS_SOL: &str = "FE455";
    /// cap-mode: the contract gates methods against two or more DISTINCT owner address
    /// fields — multiple owner authorities are deferred (a single per-contract `C_Owner`
    /// only in v1).
    pub const FE456_MULTIPLE_OWNER_AUTHORITIES_SOL: &str = "FE456";
    /// cap-mode: a synthesized cap-type/param name (`{Contract}_Owner`, `{Contract}_Deploy`)
    /// is not a legal SIGIL identifier (over the 64-byte cap) OR collides with a user
    /// record/function name (a collision is N002 at name-resolution, invisible to the FE500
    /// parse self-check, so the frontend must catch it) (IMPL-3).
    pub const FE457_CAP_NAME_COLLISION_SOL: &str = "FE457";

    // ── FE4 (Solidity → SIGIL, SOL-ERC20: full ERC20 via bounded nested mappings) ──
    // Two-level `mapping(a => mapping(b => v))` lowers to a bounded two-key map
    // (`BoundedMap2_u256_u256_u256_64`); the ERC20 `transferFrom` (an `allowance` debit
    // + a balance move) folds into ONE atomic trusted `transfer_from` across both maps.
    // A non-canonical / non-atomic transferFrom is NOT folded → its two storage writes
    // are rejected by the CEI gate (FE412); no dedicated near-miss code is needed (the
    // CEI rule is a complete safety net — every non-atomic multi-write transferFrom
    // hits it). Events are the one new precise reject:
    /// RETIRED (SOL-EVENTS): `event` declarations and `emit` statements are now parse-and-DISCARDED
    /// (events carry no SIGIL state/funds/control-flow effect, so the faithful lowering is nothing).
    /// This code is no longer emitted; an `emit` whose argument is effectful → FE481 instead. Kept
    /// defined for historical continuity (the worked-example + spec reference it).
    pub const FE459_EVENT_UNSUPPORTED_SOL: &str = "FE459";

    // ── FE4 (Solidity → SIGIL, SOL-STRUCT: `struct` → SIGIL records) ─────────────
    /// A struct CONSTRUCTION whose argument set does not EXACTLY match the declared
    /// fields (missing / extra / duplicate / wrong-arity / wrong field-type), OR a field
    /// access of a field the struct does not declare. The trusted compiler FAILS OPEN on
    /// record completeness (a record literal missing a field is silently accepted), so
    /// the frontend is the SOLE gate — a mismatch would silently zero-fill / mis-shape.
    pub const FE460_STRUCT_FIELD_MISMATCH_SOL: &str = "FE460";
    /// An unsupported struct SHAPE: a self-referential struct (a field whose type is the
    /// struct itself, directly or transitively — an infinite-size record), an empty
    /// struct (no fields), a struct field whose type is a `mapping`/array, or a struct
    /// used as a bounded-container element. Fail-closed before the malformed emission.
    pub const FE461_BAD_STRUCT_SHAPE_SOL: &str = "FE461";
    /// A `uintN` width-discipline violation: an implicit NARROWING (`uint256`→`uintN`, or
    /// `uintM`→`uintN` with m>n), MIXED-WIDTH arithmetic (`uintN op uintM`, n≠m, or `uintN
    /// op uint256`), or compound arithmetic to a `uintN` not (yet) lowered. `uintN` lowers
    /// to the `u256` carrier, so the trusted compiler cannot catch these — the frontend is
    /// the SOLE gate. (An out-of-range `uintN` LITERAL is FE430; a `uintN` in a mapping
    /// position is FE441.)
    pub const FE462_UINTN_WIDTH_SOL: &str = "FE462";
    /// SOL-CTOR: more than one `constructor` in a contract (Solidity allows exactly one; a
    /// silent drop would lose deploy-time init logic).
    pub const FE463_DUPLICATE_CONSTRUCTOR_SOL: &str = "FE463";
    /// SOL-CTOR: an unsupported constructor FORM — `payable`, a modifier or base-constructor
    /// call on the constructor, a `returns`/`view`/`pure`/`external` attribute, or an
    /// explicit `return` statement in the body (inheritance / value-transfer / a return that
    /// would short-circuit the synthesized `return __fe_c`, all out of the closed subset).
    pub const FE464_UNSUPPORTED_CTOR_SOL: &str = "FE464";
    /// SOL-CTOR: a `constructor` combined with cap-mode (`// sigil:cap-access-control`) — a
    /// deferred combination (the cap-dropped owner-field write is a type error the FE500
    /// parse self-check misses, and the cap E-2 dataflow gate does not scan the constructor).
    pub const FE465_CTOR_CAP_UNSUPPORTED_SOL: &str = "FE465";
    /// SOL-ENUM: `Name.Member` where `Member` is not a member of enum `Name`. The enum lowers
    /// to a `u256` tag, so the trusted compiler can't catch a bad member — the frontend is the
    /// SOLE gate against a silent wrong index.
    pub const FE466_BAD_ENUM_MEMBER_SOL: &str = "FE466";
    /// SOL-ENUM: an unsupported enum SHAPE — an empty enum (no members; no valid zero-default),
    /// or a duplicate member name (would silently alias two tags). Fail-closed before emit.
    pub const FE467_BAD_ENUM_SHAPE_SOL: &str = "FE467";
    /// SOL-INH: a base-constructor problem. In M1 this means a base (non-main) contract declares a
    /// `constructor` — chaining base ctor bodies + threading their args is deferred to M2, so a
    /// hierarchy with a base ctor is rejected fail-closed (never a silently-dropped base init).
    pub const FE468_BASE_CONSTRUCTOR_SOL: &str = "FE468";
    /// SOL-INH: an inheritance cycle — the contract DAG has no concrete sink (C3 can't linearize a
    /// contract that transitively inherits itself). solc rejects it too.
    pub const FE469_INHERITANCE_CYCLE_SOL: &str = "FE469";
    /// SOL-INH: ambiguous main — the file has zero or ≥2 independent CONCRETE sink contracts (one
    /// nobody inherits from). v1 translates exactly one deployable contract per file; no selector.
    pub const FE470_AMBIGUOUS_MAIN_SOL: &str = "FE470";
    /// SOL-INH: a non-linearizable hierarchy — C3's merge has no valid head (the bases impose
    /// contradictory orderings). solc rejects this with the same "Linearization impossible" error.
    pub const FE471_NON_LINEARIZABLE_SOL: &str = "FE471";
    /// SOL-INH: a state-variable SHADOW — the same field name is declared in two contracts in the
    /// hierarchy. solc bans this post-0.6; flatten rejects it so no merge path can mis-layout or
    /// mis-resolve which field a read/write targets.
    pub const FE472_STATE_SHADOW_SOL: &str = "FE472";
    /// SOL-INH: a conflicting struct/enum shape — the same type name is declared with a different
    /// shape (fields / members) in two contracts in the hierarchy; merging would pick one silently.
    pub const FE473_CONFLICTING_TYPE_SOL: &str = "FE473";
    /// SOL-INH: a `super.f()` call — virtual dispatch up the linearization. Deferred (and already
    /// reached only through an internal call, which is itself out of subset).
    pub const FE474_SUPER_CALL_SOL: &str = "FE474";
    /// SOL-INH: an abstract / bodiless function in the merged hierarchy (an unimplemented function
    /// that a concrete contract must override). Deferred — reserved for when abstract bases are
    /// body-parsed.
    pub const FE475_ABSTRACT_FUNCTION_SOL: &str = "FE475";
    /// SOL-INH: an `interface`/`library` used as an inheritance base, OR an aliased/namespaced
    /// `import` (`… as Name`, `import * …`), OR a base named in `is` not defined in this file
    /// after import-skip. Each renames/needs a symbol flatten can't faithfully resolve. (Plain
    /// `import` lines are SKIPPED — redundant in a self-contained flattened file.)
    pub const FE476_IMPORT_OR_BASE_SOL: &str = "FE476";
    /// SOL-INH: a `using X for Y;` free-function attachment — deferred (a separate feature).
    pub const FE477_USING_FOR_SOL: &str = "FE477";
    /// SOL-LEX: an inline `assembly { … }` (YUL) block. A separate low-level sub-language we do
    /// NOT translate — rejected PRECISELY (the lexer skips the balanced block so its YUL bytes
    /// don't surface as a generic "unexpected byte"), so the histogram distinguishes the assembly
    /// ceiling from supportable constructs. (FE468–FE477 are reserved for the on-deck SOL-INH
    /// inheritance rung; assembly takes FE478.)
    pub const FE478_INLINE_ASSEMBLY_SOL: &str = "FE478";
    /// SOL-LEX: a bitwise / shift operator (`& | ^ ~ << >>`). SIGIL native has NO bitwise
    /// operators (`&` is the reference sigil), so these will be STDLIB-LOWERED (`u256_and(a,b)`
    /// — the helpers already exist in `stdlib/sigil/u256.sigil`), NOT added to the trusted core.
    /// Precise-rejected for now; lowering is a deferred follow-on.
    pub const FE479_BITWISE_OP_SOL: &str = "FE479";
    /// SOL-LEX: a ternary `cond ? a : b`. Lowers to a guarded `if` (SIGIL has no if-expression),
    /// which needs short-circuit-correct ANF — a focused follow-on milestone. Precise-rejected
    /// for now.
    pub const FE480_TERNARY_SOL: &str = "FE480";
    /// SOL-EVENTS: an `emit` argument that is EFFECTFUL — it contains a call or trap-capable
    /// arithmetic (`+ - * / %`, unary `-`). The `emit` is discarded (events have no SIGIL effect),
    /// so a revert or side-effect hidden in its argument would be silently dropped (a
    /// compiles-but-different mistranslation). Fail closed: bind the computed value to a local
    /// before the emit. Plain reads (the overwhelming real-world case) are discarded freely.
    pub const FE481_EMIT_ARG_EFFECTFUL_SOL: &str = "FE481";
    /// SOL-TOKEN: a non-constant `**` (exponentiation) — only a literal decimal `base ** exp`
    /// (e.g. the `10 ** 18` decimals idiom) is constant-folded; SIGIL has no `**` operator, so a
    /// non-literal base/exponent (`x ** 2`, `10 ** decimals`) can't be folded and is rejected.
    pub const FE482_NON_CONSTANT_POW_SOL: &str = "FE482";
    /// SOL-CALLS: a statement-position internal call whose callee body contains a `return`. Flat
    /// inlining would splice that `return` into the CALLER, exiting it early — a control flow Solidity
    /// never has (a callee `return` only ends the callee). Fail-closed; deferred.
    pub const FE484_CALL_BODY_RETURNS_SOL: &str = "FE484";
    /// SOL-CALLS: internal-call inlining hit a recursion cycle (a callee transitively calls itself) or
    /// exceeded the inline-depth cap. The OZ `_transfer`/`_msgSender` spine is acyclic; this fails
    /// closed on (mutual) recursion / a too-deep call graph.
    pub const FE485_CALL_RECURSION_SOL: &str = "FE485";
    /// SOL-CALLS: an internal function used in EXPRESSION position (its value is consumed, e.g.
    /// `_msgSender()`) whose body is NOT a single `return <expr>;`. A multi-statement value-returning
    /// callee would need a temp + statement hoist that could drop a prior side effect — deferred.
    pub const FE486_CALL_VALUE_MULTI_SOL: &str = "FE486";
    /// SOL-CALLS × SOL-CAP: an internal function call in a cap-mode (`// sigil:cap-access-control`)
    /// contract. The capability E-2/H7 data-use gate (`recognize_cap_guards`) runs BEFORE the inline
    /// pass and scans only the surviving bodies + call ARGS, never a callee body — so a `msg.sender`/
    /// owner data-use hidden inside an internal callee (e.g. `log[_msgSender()]`) would bypass FE454
    /// and cap-translate a contract that uses the sender as data. Fail-closed: reject the combination
    /// (deferred). Drop the directive (use the address model) or remove the internal call.
    pub const FE487_CALL_IN_CAP_MODE_SOL: &str = "FE487";
    /// SOL-CALLS / SOL1c: a spliced body (an inlined internal call OR an inlined `modifier`) would
    /// CAPTURE one of ITS state-field references. A spliced body's bare state access is deliberately
    /// left un-renamed (to stay the shared record field), but if the HOST (the caller / the modified
    /// function) has a parameter/local of the same name (which shadows the state field in the host's
    /// scope), the spliced access silently binds to that local instead of `self.<field>` — redirecting
    /// a read/write (an access-control gate that reads the host's arg — a BYPASS — or a dropped storage
    /// write). Fail-closed: rename the host's parameter/local. (Found by the SOL-CALLS adversarial
    /// review — the internal-call pass; the same class exists in the modifier-inline pass.)
    pub const FE488_STATE_CAPTURE_SOL: &str = "FE488";
    /// SOL-CALLS: an internal function WITH parameters is called inside a `&&`/`||` short-circuit
    /// operand. Its argument let-prelude is hoisted to the enclosing STATEMENT (the inline pass runs
    /// before the `&&`/`||` ANF pass), so a trap-capable argument would be evaluated on a path Solidity
    /// short-circuits away (translate-but-trap). A 0-parameter call (`_msgSender()`) substitutes in
    /// place and is safe. Fail-closed: bind the call to a local before the condition. (Adversarial review.)
    pub const FE489_CALL_SHORTCIRCUIT_SOL: &str = "FE489";
    // FE490 was first assigned to "a local declared inside an `unchecked` block" then RETIRED (the
    // alpha-rename made that reject unnecessary); it never shipped to main with that meaning, so the
    // number was re-used below for the next reject.
    /// SOL-SAFEMATH: a `using SafeMath for uint256` is active and a `.add`/`.sub`/`.mul`/`.div`/`.mod`
    /// method call has an unsupported ARGUMENT SHAPE — a SafeMath op takes exactly ONE operand, plus
    /// an optional string revert-message for `.sub`/`.div`/`.mod` (which is dropped). Any other arity
    /// (`.add(a, b)`, a non-string 2nd arg, a 3rd arg) is fail-closed rejected here rather than folded,
    /// so the fold can NEVER silently drop or mis-index an argument into the arithmetic.
    pub const FE490_SAFEMATH_SHAPE_SOL: &str = "FE490";

    /// SOL-AIRDROP (Rung C): a dynamic array type `T[]` appears somewhere other than a
    /// function PARAMETER (a state var / local / return type), OR is a sized `[N]` / 2-D
    /// `[][]` / non-scalar-element array. Arrays exist in the subset ONLY as the airdrop's
    /// `recipients`/`amounts` parameters (emitted `BoundedVec_u256_64`); every other array
    /// use is fail-closed rejected here.
    pub const FE491_ARRAY_TYPE_SOL: &str = "FE491";
    /// SOL-AIRDROP (Rung C): a parsed airdrop `for` loop (`Stmt::AirdropLoop`) whose body
    /// is NOT the exact per-leg `M[from] -= amounts[i]; M[recipients[i]] += amounts[i];`
    /// debit/credit pair with an invariant `from` and the counter-indexed recipient/amount
    /// arrays — so `desugar::recognize_airdrop` cannot fold it to a `BatchTransfer`. Any
    /// deviation (extra statement, wrong index, non-parallel arrays, a multi-sender or
    /// external-call body) is fail-closed rejected rather than mistranslated.
    pub const FE492_AIRDROP_SHAPE_SOL: &str = "FE492";

    /// Identifier outside `^[A-Za-z_][A-Za-z0-9_]{0,63}$`, or colliding with a SIGIL
    /// keyword / the `__fe_` synth prefix.
    pub const FE420_BAD_IDENTIFIER_SOL: &str = "FE420";
    /// A numeric literal not an exact in-range `[0, 2^256)` decimal/hex u256.
    pub const FE430_BAD_NUMBER_SOL: &str = "FE430";
    /// Emitted SIGIL failed the parse self-check (internal; the translator is buggy).
    pub const FE500_INTERNAL_MALFORMED_SOL: &str = "FE500";

    // ── FE6 (Rust → SIGIL, RS0) ─────────────────────────────────────────────
    // The third foreign frontend: a Rust subset → SIGIL — memory-safe (Rust) ∧
    // capability-safe (SIGIL). RS0 is the value-semantics-only base case; its
    // guarantee (S-AUTH) is STRUCTURAL subset-closure — the emitter's output
    // alphabet names no authority-bearing op — and is the FRONTEND's to enforce:
    // an RS0 module is inner-ring, which the compiler's `effect_check` skips, so
    // the compiler does NOT certify authority-freedom. Every code is a fail-closed
    // reject that emits nothing. See docs/specs/rust-frontend-rs0.md.
    /// A Rust construct outside the RS0 subset (references/borrows, generics,
    /// traits, impls, structs, enums, `match`, closures, macros, `::` paths,
    /// method/field access, `use`/`mod`/`const`, `if`/block-as-expression, and —
    /// in the RS0 skeleton — locals/control-flow) — fail-closed catch-all.
    pub const FE601_UNSUPPORTED_RS: &str = "FE601";
    /// Input/complexity bound exceeded (bytes, nesting depth, function count).
    pub const FE602_TOO_LARGE_RS: &str = "FE602";
    /// A type annotation other than `i64`/`bool`, or a required annotation missing.
    pub const FE610_UNSUPPORTED_TYPE_RS: &str = "FE610";
    /// `/` or `%`, or an operator outside the RS0 whitelist (shift/bitwise/…).
    pub const FE611_BAD_OPERATOR_RS: &str = "FE611";
    /// A numeric literal not an exact in-range decimal i64 (suffix/radix/
    /// underscore/leading-zero/out-of-range).
    pub const FE612_BAD_NUMBER_RS: &str = "FE612";
    /// Identifier outside the SIGIL charset, raw (`r#..`), non-ASCII, over-length,
    /// or colliding with a SIGIL keyword, an emittable builtin (e.g. `trap_if`),
    /// or the `__fe_` prefix — the sole gate for emit-safety (SC-2).
    pub const FE620_BAD_IDENTIFIER_RS: &str = "FE620";
    /// An in-subset expression/statement is ill-typed (operand/argument/return
    /// type) — the sound checker rejects rather than emit a T-code (SC-7 spine).
    pub const FE630_ILL_TYPED_RS: &str = "FE630";
    /// A non-unit function has a control-flow path that does not `return`
    /// (return-path analysis; RS0-later, arrives with control flow).
    pub const FE632_NON_EXHAUSTIVE_RETURN_RS: &str = "FE632";
    /// Reassignment of a non-`mut` local or a parameter (RS0-later).
    pub const FE633_ILLEGAL_REASSIGNMENT_RS: &str = "FE633";
    /// A reference resolves to no in-scope binding (unresolved var / call target).
    pub const FE634_UNRESOLVED_REFERENCE_RS: &str = "FE634";
    /// `let` shadowing of a live binding (rejected, not renamed; RS0-later).
    pub const FE635_SHADOWING_RS: &str = "FE635";
    /// `if`/block used in value/expression position (deferred desugar; RS0-later).
    pub const FE690_EXPR_POSITION_RS: &str = "FE690";

    // ── FE6 (Rust → SIGIL, RS3: structs → records) ──────────────────────────
    /// A struct construction whose fields do not EXACTLY match the declaration
    /// (a missing / unknown / duplicate field, or a field-value type mismatch).
    /// The trusted compiler FAILS OPEN on record completeness (a record literal
    /// missing a field is silently accepted), so the frontend is the SOLE gate.
    pub const FE640_STRUCT_FIELD_MISMATCH_RS: &str = "FE640";
    /// An unsupported struct SHAPE: a tuple struct (`struct P(i64)`), a unit
    /// struct (`struct U;`), an empty struct (`struct E {}`), or a generic struct
    /// (`struct G<T>`) — all deferred, fail-closed.
    pub const FE641_BAD_STRUCT_SHAPE_RS: &str = "FE641";
    /// Field access `e.f` where `e` is not a struct, or `f` is not a field the
    /// struct declares (also a tuple index `e.0` or a method call `e.f()`).
    pub const FE642_BAD_FIELD_ACCESS_RS: &str = "FE642";

    // ── FE6 (Rust → SIGIL, RS3b: enums → enums + `match`) ───────────────────
    /// An unsupported enum SHAPE: a payload variant (`A(i64)` — deferred to a
    /// later increment), a generic enum (`enum E<T>`), or an empty enum
    /// (`enum E {}`) — all deferred, fail-closed.
    pub const FE650_BAD_ENUM_SHAPE_RS: &str = "FE650";
    /// A non-exhaustive `match`: an enum scrutinee missing variant arm(s), or an
    /// `i64`/`bool` scrutinee without a `_` catch-all. SIGIL enforces this too
    /// (T087/T088), but the frontend rejects it precisely so an ACCEPTED input
    /// never trips a compiler T-code (SC-7), mirroring RS0's own return-path gate.
    pub const FE651_NONEXHAUSTIVE_MATCH_RS: &str = "FE651";
    /// A bad enum-variant reference in a `match` arm/pattern OR in construction: an
    /// undeclared enum or unknown variant, a variant pattern on a non-enum
    /// scrutinee, a literal whose type ≠ the scrutinee, a duplicate arm, an arm
    /// after a `_` catch-all, or a deferred pattern form (a payload binding `A(x)`,
    /// a guard `if`, a range, a bare-identifier binding, or a block-bodied arm).
    pub const FE652_BAD_MATCH_ARM_RS: &str = "FE652";

    // ── FE6 (Rust → SIGIL, RS4a: `#[sigil::requires]` → refinement precondition) ─
    /// A malformed or out-of-fragment refinement predicate. RS4a admits exactly one
    /// clause of the shape `<param> <cmp> <non-negative i64 literal>` with `<cmp>`
    /// in `{ < <= > >= == != }`; anything else — a non-identifier LHS (`1 == 1`), a
    /// non-literal / negative / parameter RHS (`x < y`, `x > -1`), arithmetic, an
    /// unknown operator, more than one clause, or `#[sigil::requires]` alongside
    /// `#[sigil::cap]`/`#[sigil::effects]` — is a fail-closed reject (SR-1/2, AG-1/2/4).
    pub const FE660_BAD_REFINEMENT_RS: &str = "FE660";
    /// A refinement predicate references a name that is not a parameter of the
    /// annotated function (SR-3). The emitted `where` clause must only ever name a
    /// validated parameter, so the LHS is looked up in the parameter list here.
    pub const FE661_REFINEMENT_UNKNOWN_PARAM_RS: &str = "FE661";

    // ── FE6 (Rust → SIGIL, RS5a: `#[sigil::taint]` → information-flow `@Label`) ──
    /// A malformed / out-of-fragment `#[sigil::taint]` annotation. RS5a admits
    /// exactly `<target> = <Level>` clauses with `<Level>` in `{Public, Internal,
    /// Secret}` and `<target>` a parameter name or `ret`. Anything else — an unknown
    /// level, `SecretCT` (constant-time deferred), bad syntax, a duplicate target,
    /// more than one `#[sigil::taint]`, a non-scalar (non-`i64`/`bool`) target type,
    /// taint on a `struct`/`enum`, or taint mixed with cap/effects/requires/invariant
    /// — is a fail-closed reject (SR-T1/3/10, AG-T1/7).
    pub const FE670_BAD_TAINT_RS: &str = "FE670";
    /// A `#[sigil::taint]` target names something that is neither `ret` nor a
    /// parameter of the annotated function (SR-T2). The emitted `@Label` must only
    /// ever land on a validated parameter (or the return), so the target is looked
    /// up in the parameter list here.
    pub const FE671_TAINT_UNKNOWN_TARGET_RS: &str = "FE671";
    /// A malformed / out-of-fragment `declassify(...)` call (RS5b — the linear
    /// information-flow escape hatch). RS5b admits exactly `declassify(<scalar>)`
    /// (arity 1, an `i64`/`bool` value). Anything else — the wrong arity
    /// (`declassify()` / `declassify(a, b)`), a non-scalar argument, a
    /// `declassify_ct(...)` call (constant-time deferred to RS5c), or a `declassify`
    /// mixed with cap/effects/requires/invariant mode — is a fail-closed reject
    /// (SR-B1/2/3/6, AG-B1). The linear `Cap<Declassify>` itself is
    /// frontend-synthesized (one per call) and re-checked by `ownership::verify`.
    pub const FE672_BAD_DECLASSIFY_RS: &str = "FE672";
}

/// Hard physical bounds. Numbers align to the compiler's own constants where
/// they exist (S005 source cap = 5 MiB, S006 function cap = 10 000). The depth
/// cap is FE0-owned: the Rust parser has *no* recursion-depth cap, so totality
/// (threat T12) cannot be delegated to it.
pub mod limits {
    /// Max foreign-source bytes (mirrors compiler S005).
    pub const MAX_INPUT_BYTES: usize = 5 * 1024 * 1024;
    /// Max identifier length in bytes (threat T7).
    pub const MAX_IDENT_BYTES: usize = 64;
    /// Max nesting depth (statements + expressions, combined), charged *before*
    /// each descent AND once per node in every flat operator/postfix chain (threat
    /// T12). Deliberately LOW — and low for the same reason the Solidity frontend's
    /// `MAX_NEST_DEPTH` is: the guard must keep the *emitted* SIGIL shallow enough to
    /// survive the FE500 self-check, which re-parses it with the trusted compiler
    /// parser (~16 native frames per nesting level). A cap of 64 lets a depth-~24
    /// expression through, which overflows a 1 MiB worker-thread stack in that
    /// re-parse (measured, debug); 12 keeps the whole translate → emit → re-parse →
    /// `Drop` pipeline total on a 1 MiB stack with margin, while still admitting far
    /// deeper nesting than any real policy/contract DSL needs.
    pub const MAX_DEPTH: u32 = 12;
    /// Max function declarations per file (mirrors compiler S006).
    pub const MAX_FUNCTIONS: usize = 10_000;
    /// Max `modifier` applications on a single function (SOL1c). Real contracts use 1–5.
    /// The cap keeps the right-fold's MERGED AST shallow: each application nests the host
    /// body by ≤ the modifier-body depth (≤ MAX_NEST_DEPTH), so bounding the COUNT bounds
    /// the merged DEPTH (≤ 16×12). Without it, ~1900 nesting-modifiers build a tree deep
    /// enough that the recursive post-inline walkers (the depth re-check itself, the
    /// placeholder scan, the tree's `Drop`) overflow the native stack — a totality break.
    /// A 17th application → FE402, before the deep tree is ever built (threat T12).
    pub const MAX_MODIFIERS_PER_FN: usize = 16;
    /// The reserved prefix for every translator-synthesized name (threat T8).
    pub const SYNTH_PREFIX: &str = "__fe_";
    /// Compiler-special effect names an author `@effects` may not use (F11):
    /// `Unsafe`/`FFI` are pre-registered privilege effects (E003), `Alloc` is
    /// special-cased by the alloc-intrinsic E001 path. The full set, verified.
    pub const RESERVED_EFFECTS: &[&str] = &["Unsafe", "FFI", "Alloc"];
}

/// One emitted-SIGIL byte range paired with the foreign range it came from.
#[derive(Debug, Clone)]
pub struct SpanMapEntry {
    pub sigil: Range<usize>,
    pub foreign: ForeignSpan,
}

/// Emitted-SIGIL → foreign span map. FE0 fidelity is best-effort (anti-goal
/// T4): a lookup that misses falls back to the whole emitted span — a *total*
/// function that can never panic, never an out-of-bounds index.
#[derive(Debug, Clone, Default)]
pub struct SourceMap {
    pub entries: Vec<SpanMapEntry>,
    pub emitted_len: usize,
}

impl SourceMap {
    /// Total lookup: the foreign span for an emitted offset, or the whole
    /// emitted range when unmapped. Never panics (anti-goal T4 fallback).
    pub fn foreign_for(&self, sigil_offset: usize) -> ForeignSpan {
        for e in &self.entries {
            if e.sigil.contains(&sigil_offset) {
                return e.foreign.clone();
            }
        }
        0..self.emitted_len
    }
}

/// The successful output of a translation: emitted SIGIL text + source map.
#[derive(Debug, Clone)]
pub struct EmittedSigil {
    /// e.g. `policy.sigil` — a name to hand the compiler.
    pub source_name: String,
    /// The emitted SIGIL source text (well-formed by construction; threat T10).
    pub text: String,
    pub map: SourceMap,
}

/// A translator-level rejection, carrying an `FE`-code and the offending
/// foreign span.
#[derive(Debug, Clone)]
pub struct FrontendDiag {
    pub code: &'static str,
    pub message: String,
    pub span: ForeignSpan,
}

impl FrontendDiag {
    pub fn new(code: &'static str, message: impl Into<String>, span: ForeignSpan) -> Self {
        Self {
            code,
            message: message.into(),
            span,
        }
    }
}

impl std::fmt::Display for FrontendDiag {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {} (bytes {}..{})",
            self.code, self.message, self.span.start, self.span.end
        )
    }
}

/// Derive a legal, non-reserved SIGIL module name from a foreign source name.
/// Each frontend supplies its own deterministic fallback for unusable stems.
pub(crate) fn sanitize_module_name(source_name: &str, fallback: &str) -> String {
    debug_assert!(is_legal_module_name(fallback));

    let stem = source_name
        .rsplit(['/', '\\'])
        .next()
        .unwrap_or(source_name)
        .split('.')
        .next()
        .unwrap_or(fallback);
    let mut module: String = stem
        .chars()
        .filter(|c| c.is_ascii_alphanumeric() || *c == '_')
        .collect();
    module.make_ascii_lowercase();

    if is_legal_module_name(&module) {
        module
    } else {
        fallback.to_owned()
    }
}

fn is_legal_module_name(module: &str) -> bool {
    is_legal_identifier(module)
        && module
            .as_bytes()
            .first()
            .is_some_and(|b| b.is_ascii_lowercase() || *b == b'_')
        && module
            .bytes()
            .all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
        && !module.starts_with(limits::SYNTH_PREFIX)
        && !is_sigil_keyword(module)
}

/// Parse emitted SIGIL before returning it to the caller. Any parser diagnostic
/// is an emitter defect rather than a foreign-source policy error.
pub(crate) fn parse_emitted_sigil(
    module: &str,
    text: &str,
    code: &'static str,
) -> Result<(), FrontendDiag> {
    use sigil_compiler::parser::parse;
    use sigil_compiler::source::SourceFile;

    let sf = SourceFile::new(format!("{module}.sigil"), text.to_owned());
    let (_program, diags) = parse(&sf);
    if diags.is_empty() {
        Ok(())
    } else {
        Err(FrontendDiag::new(
            code,
            format!(
                "internal: emitted SIGIL failed the parse self-check ({} diagnostic(s)); first: {}",
                diags.len(),
                diags
                    .first()
                    .map(|d| d.message().to_string())
                    .unwrap_or_default()
            ),
            0..text.len(),
        ))
    }
}

/// A foreign frontend: parse a DSL, emit SIGIL text. Translation either
/// succeeds with well-formed SIGIL or fails with at least one `FrontendDiag` —
/// it never panics, hangs, or emits partial output (threat T12).
pub trait Frontend {
    /// Stable lowercase name, e.g. `"typescript"`.
    fn name(&self) -> &'static str;

    /// Translate `src` (named `source_name`, e.g. the `.ts` path) to SIGIL.
    fn translate(&self, src: &str, source_name: &str) -> Result<EmittedSigil, Vec<FrontendDiag>>;
}

/// Resolve a frontend by its CLI `--from <name>` value. Unknown → `None`.
pub fn frontend_for(name: &str) -> Option<Box<dyn Frontend>> {
    match name {
        "typescript" | "ts" => Some(Box::new(typescript::TypeScriptFrontend)),
        "solidity" | "sol" => Some(Box::new(solidity::SolidityFrontend)),
        "rust" | "rs" => Some(Box::new(rust::RustFrontend)),
        _ => None,
    }
}

/// Whether `s` is a legal SIGIL identifier under the FE0 charset bound
/// (threat T7): ASCII `^[A-Za-z_][A-Za-z0-9_]{0,63}$`.
pub fn is_legal_identifier(s: &str) -> bool {
    let bytes = s.as_bytes();
    if bytes.is_empty() || bytes.len() > limits::MAX_IDENT_BYTES {
        return false;
    }
    let first = bytes[0];
    if !(first.is_ascii_alphabetic() || first == b'_') {
        return false;
    }
    bytes[1..]
        .iter()
        .all(|&b| b.is_ascii_alphanumeric() || b == b'_')
}

/// Whether `s` is a SIGIL reserved keyword (threat T8). Delegates to the
/// compiler's own lexer so the keyword set can never drift from the language —
/// the audit flagged a hardcoded list as a drift hazard. `s` must already be a
/// legal identifier (see [`is_legal_identifier`]); a string the lexer does not
/// classify as `Ident` is reserved.
pub fn is_sigil_keyword(s: &str) -> bool {
    use sigil_compiler::lexer::{TokenKind, lex};
    use sigil_compiler::source::SourceFile;
    let sf = SourceFile::new("<kw-probe>", s);
    let (tokens, _diags) = lex(&sf);
    match tokens.first().map(|t| &t.kind) {
        Some(TokenKind::Ident(name)) => name != s,
        _ => true,
    }
}
