# Foreign frontend correspondence profile

**Profile:** `FFC-2026-09-07`  
**Status:** enforced for the shipped TypeScript, Rust, and Solidity frontends.  
**Machine gate:** `crates/sigil-frontends/tests/correspondence_profile.rs`.

Foreign frontends are untrusted source-to-source translators. The accepted behavior is not “the full source language behaves like SIGIL”; it is the narrower relation below: an input is inside the documented frontend grammar, the frontend emits exactly the SIGIL term specified by that profile, and the production SIGIL compiler accepts that emitted term. Any input outside the grammar, or any ambiguity the relation does not define, must fail before emission with an `FE` diagnostic.

```pins
PIN_FRONTEND_PROFILE_COUNT = 3
PIN_TYPESCRIPT_COMPILE_FIXTURES = 7
PIN_TYPESCRIPT_REJECT_FIXTURES = 22
PIN_TYPESCRIPT_REJECT_CODES = 17
PIN_RUST_COMPILE_FIXTURES = 26
PIN_RUST_REJECT_FIXTURES = 56
PIN_RUST_REJECT_CODES = 26
PIN_SOLIDITY_COMPILE_FIXTURES = 71
PIN_SOLIDITY_REJECT_FIXTURES = 184
PIN_SOLIDITY_REJECT_CODES = 55
PIN_SCALAR_ORACLE_CASES_PER_FRONTEND = 80
```

## Shared relation

For each frontend `F`, source program `S`, and emitted SIGIL program `G`:

1. `S ∈ grammar(F)` only if the relevant frontend parser, desugarer, and checker accept every token, binding, type, effect, authority, numeric, control-flow, and layout construct under the frontend's published allow-list.
2. `translate(F, S) = G` only if `G` is byte-identical to either a hand-authored golden fixture or, for the finite scalar-expression core, the independent oracle in `correspondence_profile.rs`.
3. `compile(G)` must succeed through `sigil-compiler` under the normal frontend test profile, unless the test is an explicit enforcement fixture whose purpose is to prove the trusted compiler rejects the emitted policy violation.
4. `S ∉ grammar(F)` must return one or more `FE` diagnostics and must not emit partial SIGIL. Unsupported syntax, name/scope capture, numeric/layout boundaries, control flow, effects, diagnostic preservation, and totality/size limits all have adversarial fixtures or property tests.
5. Expanding an allow-list changes the profile. The fixture counts, reject-code sets, grammar prose, and oracle evidence must be updated in the same review.

## TypeScript profile

The TypeScript frontend accepts the TS policy subset documented in `foreign-frontends.md`: top-level functions, `number`/`boolean`, nominal `interface` records, block-scoped locals, `if`/`while`, calls to declared functions, `@cap`, `@effects`, `@requires`-style policy fragments already represented in the emitted SIGIL surface, and `&&`/`||` lowered by the frontend before checking. It rejects structural typing, truthiness, unsupported operators, unsupported annotations, invalid identifiers, missing returns, unresolved references, illegal reassignment, malformed records, and mode mixes before emission.

The correspondence relation maps TypeScript values to SIGIL values by type: `number → i64`, `boolean → bool`, each accepted interface to the same-named SIGIL record with declaration-order fields, `@cap` to a synthetic moved capability parameter and terminal consumer, and `@effects` to an outer-ring effect declaration plus sorted effect row. Evaluation order is source order except for the documented short-circuit ANF transform, whose generated temp executes the right-hand operand only on the source-reachable path.

Evidence: hand-authored accepted `.ts → .sigil` goldens, compiler round-trip checks, exact `expect-fe` reject fixtures, arbitrary-input totality properties, deep-nesting limits, and the scalar-expression oracle over 80 generated programs.

## Rust profile

The Rust frontend accepts the RS profiles documented in `rust-frontend-rs0.md`, `rust-frontend-rs4.md`, and `rust-frontend-rs5.md`: a value-semantics function subset over `i64` and `bool`, selected structs/enums/matches, refinement preconditions, information-flow annotations, and the explicit `declassify` escape hatch. It rejects references, generics outside the profile, macros, modules, unsupported paths, structural capture, shadowing, unsupported operators, malformed refinements, malformed taint annotations, and bad record/enum shapes before emission.

The correspondence relation maps Rust scalar and nominal aggregate values to their same-shaped SIGIL values, maps admitted function calls to direct SIGIL calls, maps refinement predicates to SIGIL `where` clauses, maps taint clauses to parameter/return labels, and maps `declassify(x)` to the frontend-synthesized linear declassification capability pattern that the trusted compiler re-checks. Accepted Rust fixtures must also parse as real Rust under the dev-only parser oracle; that oracle is evidence for the accepted syntax set, not a runtime dependency.

Evidence: hand-authored accepted `.rs → .sigil` goldens, compiler round-trip checks, exact `expect-fe` reject fixtures, a dev-only `syn` parse oracle for accepted fixtures, trusted-compiler enforcement fixtures for stale caps/effects/taint/declassification, arbitrary-input totality properties, and the scalar-expression oracle over 80 generated programs.

## Solidity profile

The Solidity frontend accepts the SOL profiles documented in `foreign-frontends.md` and the Solidity-specific specs: one deployable contract after project/import flattening, checked Solidity `>=0.8` arithmetic over admitted unsigned integer widths, `bool`, `address` as a closed non-arithmetic type, `bytes32`, accepted structs/enums, one- and two-key bounded maps, canonical ERC20 transfer folds, selected modifiers, selected inheritance flattening, selected constructors, safe internal-call inlining, SafeMath folds, discarded pure events, and bounded airdrop loops. It rejects unsupported syntax, inline assembly, unchecked/pre-0.8 wrapping semantics, non-checks-then-effects bodies, ambiguous imports or inheritance, capture-prone modifier/internal-call shapes, address/uint confusion, unsupported maps/arrays, unsupported events, and non-canonical token movements before emission.

The correspondence relation maps Solidity scalar values to SIGIL carriers with frontend-owned width/address discipline, maps storage fields to the emitted record fields or bounded maps, maps `require`/`assert`/`revert` to `trap_if`, maps accepted transfer idioms to trusted bounded-map atomic helpers, maps `msg.sender` to the explicit `__fe_sender` parameter in the address model, and maps opt-in access-control patterns to unforgeable SIGIL capabilities. The relation deliberately treats bounded-map capacity traps and always-checked `unchecked` arithmetic as documented fail-loud divergences; where the subset cannot make a divergence fail-loud and faithful, it rejects.

Evidence: hand-authored accepted `.sol → .sigil` goldens, compiler round-trip checks, exact `expect-fe` reject fixtures, Solidity-specific property tests for integer-width lowerings, inheritance/project flattening tests, ERC20 adversarial tests for near-miss token movements, arbitrary-input totality properties, and the scalar-expression oracle over 80 generated programs.

## Review gate

Every allow-list expansion requires explicit review and renewed evidence. A valid expansion updates this profile, the relevant grammar/semantics prose, accepted and rejected fixtures, reject-code coverage, and any scalar/property oracle affected by the new construct. A change that only makes the translator accept more syntax, without updating this profile and the evidence pins, is a failed correspondence change.
