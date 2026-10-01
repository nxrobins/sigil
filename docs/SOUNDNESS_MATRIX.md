# SIGIL soundness matrix

This matrix connects each high-priority security claim to production enforcement, independent
pressure, negative canaries, composition coverage, exclusions, and self-host status. It is a map of
evidence, not a substitute for the tests it names.

Status meanings:

- `enforced`: production enforcement and a direct negative canary exist for the declared claim.
- `bounded`: the declared subset is enforced, but an explicit evidence or composition risk remains.
- `gap`: a known production or release-gate requirement is incomplete.

### SND-IFC-001 [P0]

- **Claim:** Accepted programs cannot move `Internal`, `Secret`, or `SecretCT` values to a lower
  declared data sink without explicit declassification, within the static policy in
  `SECURITY_MODEL.md`.
- **Enforcement:** `crates/sigil-compiler/src/taint_check.rs` checks bindings, returns, direct and
  indirect call boundaries, effect-operation parameters and clauses, state writes, send/ask/spawn
  boundaries, FFI, structured pc-taint, joins, and early-exit continuations. Malformed partial typed
  shapes, including positional mismatches in recovered generic calls, fail closed with I013.
  Heap CONTENTS are floored rather than trusted (`CLAIMS.md` claim 53): two monotone per-function
  floors join every raw load and every typed memory read, raised by FFI, by every non-@Public
  memory write and its address operands, by what a callee can have written and read, by closure
  bodies flowing back to their construct site, by the actor dispatch fixpoint over persistent
  state, and by string literals and f-strings as reads of shared static data (switches S1–S11,
  all on except S3, each `pub const` and measurable off). A pointer that reaches a sink UNREAD
  (a tool returning its output buffer to the host) carries the M6 region taint, raised by every
  raw write for every operand that is a regioned local, by a callee through the parameter slots
  it can write through, and by a closure body at its construct site; the region facts are
  joined at every control-flow merge (loop back-edges, `if`/`match` arms, block shadows), so a
  pointer rebound on one path is attributed to every candidate region at the store.
- **Trusted assumptions:** Typed-AST labels and actor signatures are correct; all relevant typed
  expression and statement variants are visited; runtime behavior preserves the checked boundary.
  Host shims write guest memory only into fresh bump-pointer cells (SR-024: censused, with an
  anti-stub, rather than assumed).
- **Independent oracle/model:** The Lean taint calculus proves its own trace property;
  `selfhost/taint_check.sigil` differentially covers a curated scalar/record/closure subset. The
  Lean gate has no memory cell, so the heap floors are Rust-only (SR-022).
- **Negative canary:** @test:implicit_flow_secret_guarded_break_leak,
  @test:direct_call_rejects_secret_into_public_parameter,
  @test:abortive_effect_clause_preserves_secret_parameter_taint,
  @test:legacy_handle_checks_every_nested_statement,
  @test:extern_call_rejects_secret_argument, @test:spawn_secret_cap_into_public_init_is_rejected,
  and @test:every_wrong_generic_call_arity_is_i013_not_an_abort. Heap floors:
  @test:ffi_digest_read_through_predicted_address_is_t001,
  @test:secret_store_read_back_through_fresh_region_is_t001,
  @test:public_value_stored_at_a_secret_address_is_t001,
  @test:f_string_compare_after_a_secret_store_is_t001,
  @test:callee_storing_its_own_secret_through_a_returned_caller_pointer_is_t001, and
  @test:pointer_rebound_across_a_loop_back_edge_taints_the_returned_region_is_t001 (the region
  facts across a loop back-edge), each with an accepted clean twin.
- **Composition coverage:** @test:while_continue_skips_reset_is_rejected,
  @test:continue_inside_match_arm_in_loop_is_rejected, @test:break_bypasses_declassify_barrier,
  @test:indirect_call_rejects_non_public_argument_without_taint_contract,
  @test:abortive_effect_clause_checks_every_nested_statement, and
  @test:region_checks_every_nested_statement. @test:malformed_partial_typed_call_fails_closed_in_taint
  pins the public recovery interface, while
  @test:taint_checker_source_has_no_release_abort_primitives prevents release-abort primitives
  from returning to the taint pass. Heap floors across boundaries:
  @test:callee_typed_write_of_its_own_secret_through_mut_is_t001 (callee store),
  @test:stdlib_from_bytes_over_a_secret_materialization_is_t001 (callee load, composed with the
  real stdlib shape), @test:grant_closure_writing_its_own_secret_into_a_capture_is_t001 (closure),
  @test:handler_reading_state_another_handler_wrote_at_a_secret_index_is_t001 (actor dispatch),
  and @test:named_callee_reading_a_string_literal_after_a_secret_store_into_it_is_t001 (shared
  static data).
- **Known exclusions:** Termination observation, environmental side channels, and arbitrary foreign
  behavior. Higher-order function types do not encode taint contracts, so non-Public indirect-call
  arguments are conservatively rejected. Conservative false rejects are permitted. Heap-content
  precision is address-blind: no floor knows WHICH cell a store hit, so the coarse rules' false
  positives are pinned as counted costs
  (@test:named_callee_reading_its_own_fresh_array_after_callers_secret_store_is_a_counted_false_positive).
  Three heap channels stay OPEN, each pinned as an exact accept so it cannot drift silently: the
  sink-INSIDE-callee form of the interprocedural load direction (S3 closes it at a measured corpus
  cost and is kept off; @test:helper_sinking_a_raw_read_inside_itself_after_callers_ffi_is_the_interprocedural_boundary,
  @test:closure_sinking_an_aggregate_read_inside_itself_after_a_secret_write_is_open), the
  allocation-size channel through the bump pointer
  (@test:secret_allocation_size_observed_through_the_bump_pointer_is_open), and the UNREGIONED
  pointer through the returned-pointer sink: the M6 region model regions only locals bound to
  `alloc`, or to `+`/`-` arithmetic over `alloc` calls and regioned locals (`alloc(8)`,
  `alloc(8) + k`, `out + i`), so a raw write through any other pointer expression — a parameter
  (including a tool's own `input_ptr`, the host's buffer), a callee's result, arithmetic other
  than `+`/`-`, a pointer reloaded from memory or read out of an aggregate or a state field — is
  attributed to no region and the returned buffer carries the secret unlabeled
  (@test:secret_stored_through_the_parameter_pointer_then_returned_is_open,
  @test:pointer_smuggled_through_an_array_element_then_stored_through_is_open,
  @test:secret_stored_through_a_record_field_pointer_then_returned_is_open). The region bounds
  neither the packed LENGTH the host reads — an over-long length on a clean neighbouring buffer
  exposes the tainted region beside it — nor a `+`/`-` offset that leaves its buffer, so the
  returned-pointer sink is open on those two shapes as well (disclosed, not pinned). A sink
  violation inside an assignment place's index reports I013 rather than T001 (SR-023).
- **Self-host status:** Curated parity only. Control joins, early-exit continuation taint, match
  guards, actor/spawn boundaries, and closure-value taint emit an explicit unsupported verdict,
  which the composed self-host pipeline rejects. The heap floors have no self-host shadow.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence; SR-022 (heap floors are
  Rust-only), SR-023, SR-024; SR-025, SR-026, SR-027 for the three open heap channels (#764).

### SND-CT-001 [P0]

- **Claim:** `SecretCT` cannot drive supported source-level variable-time control, address,
  division, shift-amount, FFI, actor-boundary, or allocation operations.
- **Enforcement:** `crates/sigil-compiler/src/taint_check.rs` emits T020-T034 (T033 is the `str`
  content compare, CT018; T034 the shift AMOUNT, CT008 — the shifted value is exempt);
  `crates/sigil-compiler/tests/taint_ct_audit.rs` checks emitted Wasm patterns.
- **Trusted assumptions:** The source-to-Wasm lowering preserves the audited operation classes and
  host imports do not add secret-dependent behavior.
- **Independent oracle/model:** Curated self-host T-code parity plus a separate Wasm byte audit.
- **Negative canary:** @test:ct001_if_on_secret_ct_rejected,
  @test:ct002_while_guard_tainted_inside_loop_rejected, @test:ct005_index_by_secret_ct_rejected,
  @test:ct008_shl_by_secret_ct_amount_rejected,
  @test:closure_parameter_taint_is_enforced_inside_body,
  @test:direct_call_rejects_non_ct_secret_into_secretct_parameter,
  @test:spawn_secretct_cap_is_rejected_t028.
- **Composition coverage:** @test:ct012_closure_capturing_secret_ct_branch_rejected and the
  `taint_constant_time_phase_b` generic/closure corpus.
- **Known exclusions:** Microarchitectural, OS, host, speculative, cache, power, and EM channels.
- **Self-host status:** Curated T020-T032 parity (T028 demoted as actor-only); T033 (CT018) and
  T034 (CT008) are oracle-only — the shadow has no `str ==` or shift rule, and the differential
  filters both sides to its 13-code core set, so the shadow lags the oracle there rather than
  disagreeing; actor and unsupported control distinctions reject explicitly rather than widening
  the parity claim.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence.

### SND-CAP-001 [P0]

- **Claim:** Source cannot forge capability authority, and authority delivered to a checked
  call/spawn/send/return sink must satisfy the sink obligation.
- **Enforcement:** Type construction membrane, `crates/sigil-compiler/src/air_capability_v2`, the
  solver-independent slot escape gate `crates/sigil-compiler/src/slot_escape.rs` (C013: a
  possibly-restricted capability may be put only into a confined `slot_new` local of the same
  function, so every aliasable slot — parameter, state field, copy — holds only full-authority
  puts and the variable-keyed Z3/Lean slot meets stay sound), the state-cap origin gate in the same
  module (C014: a cap-typed actor-state field may only be assigned a capability with a recognised
  full origin, so "a capability read from actor state is full" — which C013, the prover and the
  Lean verifier all classify it as — is enforced at the store rather than assumed), and runtime
  capability tables.
- **Trusted assumptions:** Authority registries assign stable bits; capability lowering identifies
  every sink; Z3 answers only inside the guarded fragment; parameters of non-closure functions
  are full because every call/spawn/message/return sink requires the full mask (SR-002); lowering
  kinds every capability value `Cap`/`StateCap` (the one kind test C014 and the prover share) and
  every actor-state store is an `AirStmt::StateWrite` (the empty-`init` positional population is
  runtime-written from spawn-sink parameters and carries no store).
- **Independent oracle/model:** Lean capability calculus, self-hosted pure-workload/verdict shadow,
  and runtime capability-table state-machine properties.
- **Negative canary:** @test:the_sole_prover_rejects_every_capability_rejection_fixture,
  @test:cap_forgery_rejected_by_frontend,
  @test:restricted_put_through_a_callee_slot_parameter_is_c013,
  @test:restricted_put_into_an_actor_state_slot_is_c013,
  @test:restricted_put_through_a_copied_local_slot_is_c013,
  @test:take_and_put_back_through_an_actor_state_slot_is_c013_with_no_restrict,
  @test:take_and_put_back_through_a_slot_parameter_is_c013_with_no_restrict,
  @test:init_restricting_its_parameter_into_a_state_cap_is_c014,
  @test:a_state_cap_narrowed_in_init_cannot_reach_a_state_slot (the init-narrowed state cap that
  reached a sink directly and through a state slot on `main`), and, on the solver lane,
  @test:slot_alias_through_callee_parameter_is_outside_the_meet_and_closed_by_c013 (the prover
  alone still accepts the aliased put; the gate is what rejects it).
- **Composition coverage:** `cap_aggregate_smuggle.rs`, `ring_cap_aggregate_smuggle.rs`,
  @test:cap3_reject_matches_oracle, and @test:cap_sink_contract_is_deliberately_full_mask cover
  generics, aggregates, rings, all sink kinds, and the conservative body-independent contract.
- **Known exclusions:** At most 32 authority bits; capability parameters cannot declare a reduced
  authority subset; Lean does not model the full `mintable_by` policy; a capability without a
  full-authority origin the slot escape gate recognises (a non-closure parameter, `mint`, an
  actor-state read or a DIRECT call result, directly or through `let`/`draw`/`split`; a
  closure-call or FFI result is not one) cannot be put into an aliasable slot (C013) and cannot be
  stored into a cap-typed actor-state field (C014), in `init` or anywhere else. Both exclusions are
  wider than "restricted": they cover the result of ANY `slot_take`, full or restricted, and any
  unclassifiable origin, so with NO `.restrict` in the program C013 rejects take-and-put-back
  through an actor-state slot or a `Slot<Cap>` parameter, a refill cycle (take, draw, put back),
  moving a capability between two state slots, and relaying one out of a slot into another
  aliasable slot, and C014 rejects `init` storing a `slot_take` result. C014 also rejects storing
  a `restrict_deadline(..)` result, even into a field already typed at the narrower deadline: the
  call lowers to the same `CapRestrict` node as `.restrict`. Put a recognised-origin
  capability instead, keep the slot a confined `slot_new` local, store the bare `init` parameter,
  and restrict the `slot_take` result or the state read at the point of use (SR-020 and SR-021
  record the measured accept/reject sets and which verdicts are default-lane only).
- **Self-host status:** Pure workload and verdict parity on a curated cap-only subset.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence; SR-020 (closed) records
  the slot-alias hole and why the slot meets stay variable-keyed; SR-021 (closed) records the
  init-narrowed state-cap hole that made the state-read origin a premise until C014 enforced it.

### SND-OWN-001 [P0]

- **Claim:** A linear value cannot be consumed twice or moved while borrowed within the ownership
  analysis's modeled control-flow state.
- **Enforcement:** `crates/sigil-compiler/src/ownership.rs` over AIR.
- **Trusted assumptions:** AIR move/use classification is exhaustive; block identity and every
  encoded CFG reference are validated before state propagation.
- **Independent oracle/model:** Lean affine typing and `selfhost/own_check.sigil` on the declared
  straight-line cap subset.
- **Negative canary:** @test:own0_oracle_pins, @test:own0_cfg_move_state_is_propagated,
  @test:own0_cfg_borrow_state_is_propagated, @test:own_verdict_parity, and
  @test:malformed_air_cfg_fails_closed_without_panicking.
- **Composition coverage:** Branch joins, returning branches, loop back-edges, spawn, call, send,
  return, restrict, borrow, duplicate arguments, unreachable bad edges, and structural branch and
  dispatch references are covered in `own_check_differential.rs`.
- **Known exclusions:** Borrow state is conservative because AIR carries no explicit borrow-end node;
  the self-host shadow remains restricted to straight-line cap-only programs.
- **Self-host status:** Curated straight-line O001/O007 parity across every supported consuming site;
  CFG analysis is production-only.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence; malformed-AIR closure is recorded as SR-015.

### SND-EFFECT-001 [P1]

- **Claim:** A supported call or operation cannot exercise an effect outside the enclosing declared
  and handled effect row.
- **Enforcement:** `crates/sigil-compiler/src/effect_check.rs`, effect-handler visibility walk, and
  post-desugar residue gate.
- **Trusted assumptions:** Call resolution and effect registration are complete; desugaring cannot
  introduce an unchecked operation after the security walk; for a monomorphized instance, and for
  a closure lambda-lifted while an instance body is re-checked, the walk keys the inner-ring
  exemption and the E002 trust authority on the MEET of the generic's defining module and every
  module whose scope resolved names in the re-checked body (`TypedProgram::governing_context`:
  exempt only if all are inner-ring, trusted only if all are `#[trusted]`) — never on `modules[0]`
  merely because the instance is filed there, never on the name prefix (the CALLING module for a
  free-fn instance), and never on the definer alone, since a free-fn instance body resolves its
  callee names in the caller's scope and an impl-method body falls back to the checked module's
  `use` scope. The recorded resolving scopes are assumed complete: they are the module whose
  function sigs the re-check context used and the module whose `use` scope and ring the call
  resolver consulted, which are the only name sources `call_resolve.rs` reads.
  No inner-ring primitive performs an effect that reaches the host; that is what makes the exemption
  acceptable for non-generic inner-ring functions and for all-inner instances alike. That is the
  defensible form of the assumption: the inner ring is NOT effect-free — `alloc` is an inner-ring
  intrinsic performing the registered `Alloc` effect, exempt there and E001 in the outer ring
  (@test:inner_ring_alloc_is_exempt_outer_fires_e001) — so inner-ring allocation is simply never
  charged to a declared row. The host-boundary assumption rests on two fences: R003 (inner-ring
  `extern` call, @test:inner_ring_extern_call_is_fenced_by_r003) and R004 (direct inner→outer call;
  only `grant` crosses, @test:inner_to_outer_cross_ring_call_is_fenced_by_r004). E003
  (@test:inner_ring_privilege_row_is_fenced_by_e003) is row hygiene, not a host-boundary fence: it
  rejects `FFI`/`Unsafe` NAMED in a declared row, so it does not reach a row-less inner-ring `handle
  Unsafe` block, and its validator walks free `FnDef` items only, leaving inner-ring impl methods
  outside it entirely.
- **Independent oracle/model:** `selfhost/effect_check.sigil` parity for E001/E002 and Lean
  `effect_safety` (synthesized rows) plus the `Chk` checking judgment
  (`Chk.effect_safety_declared`, `Chk.app_latent_bounded` in `EffectRows.lean`) for declared-row
  and latent-row containment.
- **Negative canary:** @test:sh_effect_reject_matches_oracle and effect-handler E004 residue tests;
  instance routing: @test:inner_first_outer_generic_fn_is_effect_checked,
  @test:inner_first_outer_generic_impl_method_is_effect_checked and
  @test:inner_first_outer_ffi_chain_rejects_without_certificate pin that an outer-ring generic's
  instance is checked under the outer ring whatever module sorts first (before the routing fix
  the instance was filed under the first module and an inner-ring first module exempted it), with
  @test:nongeneric_twins_prove_the_detectors_fire as the SC-P4 control;
  @test:use_imported_generic_is_checked_under_definer_trust pins that a `use`-imported generic's
  instance (named after the CALLING module) is E002-checked under a meet that includes the
  untrusted DEFINER, with @test:nongeneric_and_same_module_twins_prove_e002_fires as its control;
  @test:closure_lifted_in_an_instance_is_checked_under_definer_trust pins the same for a `handle
  Unsafe` wrapped in a closure inside that generic (the closure carries the caller's name prefix),
  with @test:closure_trust_twins_prove_e002_fires_through_a_closure as its control;
  @test:review_repros_borrowing_a_trusted_modules_authority_are_e002 pins the remaining round-2
  review repros as exact E002 (a trusted caller sorting first, a `handle Unsafe` two closures
  deep, a closure lifted after a nested trusted instance's re-check, and a trusted definer
  sorting first whose `handle Unsafe` names the untrusted caller's shadowing helper), each beside
  a non-generic control on the same layout. The meet's
  other half — the definer alone is NOT the authority — is pinned by
  @test:trusted_generic_instantiated_from_untrusted_caller_is_e002 and
  @test:trusted_generic_closure_instantiated_from_untrusted_caller_is_e002 (a trusted generic
  instantiated from an untrusted module holds no trust; trusted-caller control accepted),
  @test:caller_scope_helper_under_trusted_generic_handle_is_e002 (a trusted generic's `handle
  Unsafe` would run the untrusted caller's same-named helper),
  @test:impl_method_use_scope_fallback_is_governed_by_the_meet (a trusted generic impl method's
  `handle Unsafe` reaching an untrusted module through the caller's `use` scope; non-generic twin
  exactly T062), and
  @test:inner_ring_generic_leak_is_exempt_only_when_every_governing_module_is_inner /
  @test:inner_ring_generic_handle_unsafe_is_exempt_only_when_every_governing_module_is_inner (an
  inner-ring generic instantiated from an outer module is walked: E001 for an FFI chain, which is
  therefore uncertified, E002 for an untrusted outer module discharging FFI in either module
  order; the outer-ring definer on the same layout is the SC-P4 control).
- **Composition coverage:** @test:sh_effect_stdlib_clean_parity_and_floor plus
  `generic_impl_effects.rs`, `effect_handlers.rs` and `effect_ring_routing.rs`.
- **Known exclusions:** the Lean⇄Rust relation is a reviewed correspondence by shared fixture id
  (the higher-order E001 pair `LSD-E001-hof` / `LSD-ACC-E001-hof` ties `EffectRows.lean`'s `Chk`
  witnesses to the same-shape `.sigil` program; the direct-call E001 fixtures stay Rust-only), not
  a mechanized bridge; generic call-site instantiation binding is a trusted assumption; the
  self-host shadow covers E001/E002, not the full handler diagnostic surface. Inner-ring modules
  (the default ring when no `#[ring]` attribute is written) are exempt from the effect check
  wholesale: an undeclared-effect call, an `alloc` under an empty row, a closure DEFINED AND APPLIED inside one
  inner-ring function under an empty row, and a `handle Unsafe` compile clean there where the
  outer ring rejects with E001/E001/E001/E002. The closure statement is scoped to that shape
  because that is the shape the pin measures; it is not a statement about effectful closures in
  general, and the argument-to-a-generic-callee shape is governed by the second emitter below.
  For non-generic code the exemption is confined to the inner ring (an
  outer-ring fn placed after an inner-ring module still rejects with E001,
  @test:outer_ring_nongeneric_fn_after_inner_module_still_fires_e001). It fails OPEN if an
  inner-ring effect-performing primitive is ever added; it is pinned beside its fences by
  @test:inner_ring_direct_call_is_exempt_outer_fires_e001,
  @test:inner_ring_closure_apply_is_exempt_outer_fires_e001,
  @test:inner_ring_alloc_is_exempt_outer_fires_e001 and
  @test:inner_ring_handle_unsafe_is_exempt_outer_fires_e002.
  GENERIC CODE (BUG-5b, closed in this tree): monomorphized generic instances are filed under the
  program's first module regardless of their defining module (`type_check/mod.rs`, the `else { 0 }`
  owner arm), and on `main` at `ae026aec` the effect and ring checks keyed on the filing module's
  ring. Three directions were measured there, all against a first module carrying the opposite ring
  from the generic's own: (1) with an inner-ring first module an outer-ring generic fn or generic
  impl method escaped the effect check entirely, and R001 and R002 with it; (2) with an outer-ring
  first module an inner-ring generic escaped R003 (the ring-code side of both directions, with
  R004/R006 as unaffected controls, is pinned under SND-RING-001); (3) with an outer-ring first
  module an inner-ring generic WAS effect-checked: E001 and E002 fired on inner-ring source whose
  byte-identical non-generic twin compiled clean (fail-closed, a scope surprise rather than a hole).
  The governing meet closes all three. NON-generic inner-ring functions stay exempt from the effect
  walk by design (the inner ring has no effect rows, E003), so the claim is an outer-ring property.
  For generic code the meet decides, and it only ever removes privileges relative to any single
  governing module: an instance is exempt only when EVERY governing module is inner-ring, i.e. an
  inner-ring generic instantiated from inner-ring code, which the effect checker then treats
  exactly as its non-generic twin (exempt; the pre-routing compiler rejected that layout with
  E001/E002 only because the instance was filed under an unrelated outer first module, direction
  (3)), and it holds E002 authority only when every governing module is trusted. The meet decides
  the checking, not the emission: the instance of direction (3) is still emitted in the outer ring
  of the first module it is filed under, so the AIR-level placement gate refuses its inner caller's
  call with exactly R007 (SR-018) and that layout does not compile until instances are emitted into
  their governing ring (issue #768; landed this way by the
  author's decision of 2026-10-01). `effect_ring_routing.rs` pins each such meet-accepted layout
  at two layers: the checker layer (before AIR) accepts it, the pipeline is exactly {R007}.
  Consequently a trusted generic that
  uses `handle Unsafe`, bare or in a closure, is rejected when instantiated from an untrusted
  module, in every module order, although its non-generic twin is accepted; that over-rejection is
  the price of the fail-closed rule and is SR-019's follow-up. The meet is consulted by
  `check_effects` and `check_rings` only. The type-check pass's generic call-site row check
  (`bind_and_check_effect_rows`, the second E001 emitter) reads no module, no ring and no trust, so
  the meet neither enables nor suppresses it: an effectful closure passed to a generic callee's
  concrete row inside an all-inner generic stays exactly E001, as in its non-generic twin, with a
  pure-closure control accepted
  (@test:inner_ring_definer_accept_does_not_reach_the_ring_blind_row_check). The certificate's
  `effects_required` (a program-wide union of declared rows) was unaffected throughout. The
  self-host shadow (ET-EFF-5) does not cover generic code by construction: it skips inner modules
  wholesale and scans only non-generic outer fns.
SCOPE OF THE EXEMPTION, STATED
  EXACTLY: all of the above is about `effect_check.rs`, which is not the only pass that raises
  E001. The type checker's generic call path (`bind_and_check_effect_rows`,
  `type_check/expressions/calls.rs`) raises E001 for row contravariance on a generic callee's
  `Fn`-typed formal, and it is ring-blind — the type-check pass takes no ring and consults no
  module ordering. Measured: an effectful closure passed to a generic callee's concrete `! { }`
  formal is exactly {E001} under the default (inner) ring, an explicit `#[ring(inner)]`, and
  `#[ring(outer)]` alike (@test:generic_callee_concrete_row_fires_e001_in_every_ring), and still
  exactly {E001} when every module is inner-ring, where the monomorph routing above would end in
  the wholesale skip (@test:generic_callee_e001_is_not_the_monomorph_routing_path). It is
  fail-closed and narrower than "generic callees are effect-checked": a row-variable formal binds
  the argument's row and is clean
  (@test:generic_callee_row_variable_absorbs_the_effectful_argument), a pure closure argument is
  clean (@test:generic_callee_pure_closure_argument_is_clean), and the non-generic twin is a type
  error, not an effect error (@test:nongeneric_callee_effectful_closure_argument_is_t071_not_e001).
  A `handle` at the call site does not silence it
  (@test:handle_at_the_call_site_does_not_silence_the_generic_row_check). This emitter narrows no
  claim in this row, but it means no "E001 fires only in ring X" sentence is sound; only E002 is
  scoped by the ring skip, having its single emitter in `effect_check.rs`.
- **Self-host status:** Curated E001/E002 parity and a stdlib clean floor.
- **Status:** `bounded`: the bound this status names is the per-function row guarantee, which holds
  for non-generic code in the outer ring and, for generic code, under the governing meet (Known
  exclusions; SR-019); an instance filed in another ring than its caller is refused at emission
  (R007, #768) rather than checked-and-emitted.
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence; SR-019 records why a
  generic instance needs a governing meet and the follow-up that would retire it. The first-module
  routing gap formerly tracked in `../tests/attack/KNOWN_GAPS.md` ("Effect-check ring routing") is
  closed by the meet; that entry keeps the measurements as history.

### SND-RING-001 [P1]

- **Claim:** Outer-ring code cannot own capabilities and inner-ring code cannot directly exercise
  foreign authority outside the declared crossing rules.
- **Enforcement:** `crates/sigil-compiler/src/ring_check.rs`, type-check crossing rules, and
  ring-specific Wasm memories/import sets.
- **Trusted assumptions:** Every module/function has the correct ring and the emitted import/memory
  partition matches the checked program. For the R001-R003 walk, a monomorphized instance (and a
  closure lifted while one is re-checked) is governed by the MEET of its defining module and every
  module whose scope resolved names in its body: it is held to the outer-ring rules (R001/R002) if
  ANY governing module is outer-ring and to R003 if ANY is inner-ring, so an instance straddling
  both rings gets both rule sets; a non-instance is governed by its filing module. For the two-ring
  Wasm partition the ring is still the FILING module's, and an instance is filed under
  `modules[0]`, so the emitted ring of an instance defined in a later module of the other ring is
  NOT a checked ring; every lowered call between such an instance and a caller emitted in the other
  ring is refused at emission with exactly R007, so those layouts do not compile, even where the
  meet accepts them, until instances are emitted into their governing ring
  (issue #768). The two-ring emitter formerly indexed calls
  by global FuncId inside a per-ring
  index space and sized each ring's `call_indirect` table compactly; that pre-existing emitter
  defect is closed as SR-018 (per-ring `FuncId -> index` maps, a program-spanning table, and the
  AIR-level R007 gate `ring_check::check_air_ring_placement` for a monomorph-induced cross-ring
  call), so this row no longer carries a branch reference for it.
- **Independent oracle/model:** `selfhost/ring_check.sigil` differential parity on R001/R003 and
  runtime host/import tests.
- **Negative canary:** @test:sh_ring_reject_matches_oracle; instance routing:
  @test:outer_first_inner_generic_extern_call_is_r003 pins that an inner-ring generic's instance
  calling an extern is R003 with an outer-ring module sorting first (before the routing fix the
  instance was checked under the outer module it was filed in), with
  @test:nongeneric_twins_prove_the_detectors_fire as the SC-P4 control; and
  @test:outer_generic_resolving_an_inner_callers_extern_is_r003 pins the meet's ring half: an
  inner-ring module that routes an `extern` through an OUTER-ring generic (whose body resolves the
  extern in the inner caller's scope) is exactly R003 in both module orders — the definer's ring
  alone applied only the outer rules and accepted it; and
  @test:outer_ring_cap_rules_follow_the_governing_context_for_generics pins that R001 and R002
  read the same governing context: an outer-ring generic owning a cap, or returning a
  cap-reference type, is exactly R001 / R002 with an inner-ring module sorting first (main
  `ae026aec`: accepted), each beside its non-generic twin; an inner-ring generic instantiated from
  its own module with an outer module first passes the ring check as its twin does (main: R001 /
  R002, a filing artifact) and is refused at emission with exactly R007, its instance being filed
  in the outer ring (both layers pinned; #768); and an inner generic owning a cap, or returning a
  cap-reference type,
  instantiated from an OUTER caller with the inner definer sorting first is exactly R001 / R002
  under the meet (main: accepted; the non-generic twins do not even resolve there, exactly T062).
- **Composition coverage:** `ring_cap_aggregate_smuggle.rs`, `effect_ring_routing.rs` and runtime
  host-boundary tests.
- **Known exclusions:** R002 is pre-empted by a type error in the differential corpus; R004 is
  enforced outside the ring shadow. GENERIC CODE, HISTORY AND PINS: on `main` at `ae026aec` every
  code `ring_check.rs` emits (R001, R002 and R003) escaped for generics, because `ring_check` keyed
  all three on the ring of the module a function is FILED under, and a monomorphized generic
  instance (free fn or impl method) is filed under the program's first module (`type_check/mod.rs`,
  the `else { 0 }` owner arm) rather than its defining module. Measured against the compiler built
  from `main` at `ae026aec`, each generic against its byte-identical non-generic twin, in both
  first-module orders: (1) R001: with an INNER-ring first module, an outer-ring generic that owns a
  cap (as a parameter, as its return type, or `let`-bound; free fn or generic impl method) compiled
  with an EXACTLY EMPTY set; the twin was exactly {R001}. (2) R002: same order, an outer-ring
  generic returning a cap-reference-bearing closure type (`-> Fn(i64) -> &Tool`) was exactly EMPTY;
  the twin exactly {R002}. A bare `-> &Tool` is not a probe of R002: a type error (T253) pre-empts
  it in both twins. (3) R003: with an OUTER-ring first module, an inner-ring generic whose body
  calls an `extern` (result bound `@Internal` so no taint code pre-empts; free fn or generic impl
  method) was exactly EMPTY; the twin exactly {R003}; nothing else caught it (R004 does not apply,
  there is no cross-ring call since the `extern` is declared in the inner module itself; E003 does
  not apply, no privilege effect is named in a row; the taint gates are silent by the `@Internal`
  binding). (4) The mirror of each was fail-CLOSED on legal generics: an outer-ring `#[trusted]`
  generic calling an `extern` was exactly {R003} after an inner-ring first module, and after an
  outer-ring first module an inner-ring generic owning a cap was exactly {R001} and one returning a
  cap-reference closure type exactly {R002}, where each twin is clean. Under the governing meet
  (Trusted assumptions above) all four directions now give the twin's verdict, and the pins that
  recorded the escapes were flipped in the landing that merged the meet: (1) is exactly {R001}
  (@test:ring_routing_r001_outer_generic_after_inner_first_module_matches_its_twin), (2) exactly
  {R002} (@test:ring_routing_r002_outer_generic_after_inner_first_module_matches_its_twin), and (3)
  exactly {R003} (@test:ring_routing_r003_inner_generic_after_outer_first_module_matches_its_twin).
  The legal generics of (4) pass the ring check like their twins, but each instance is filed in the
  other ring than its caller, so the pipeline refuses each at emission with exactly {R007}
  (@test:ring_routing_mirror_direction_rejects_legal_generics; twins clean): still fail-closed on
  legal code, now by the stated R007 bound rather than a misapplied ring code, until #768 emits
  instances into their governing ring. NOT AFFECTED,
  measured the same way: R004 (raised by the type checker against the DEFINING module's ring, both
  call directions) and R006 (a module attribute) give identical sets for a generic and its twin in
  both orders (@test:ring_routing_r004_and_r006_do_not_escape_for_generics). R005 is registered but
  never emitted; R010-R013 are AIR-level invariants with no ring key. An UNINSTANTIATED generic
  yields no typed function at all (the type checker builds functions for templates only through
  their instances), so it has nothing to check or emit and is not an escape. R004 does not reach
  GENERIC free-fn calls at all: a generic free fn resolves program-wide by bare name, so inner-ring
  code can call an outer-ring generic with no `use` and no `grant` (pinned as it stands by
  @test:known_gap_generic_free_fn_call_bypasses_use_and_r004; recorded in
  `../tests/attack/KNOWN_GAPS.md`). The meet above bounds what such an instance may do; it does not
  make the call itself a checked crossing. End to end, the emission gate refuses that call with
  R007 when the instance happens to be filed in the outer ring (the outer definer sorting first);
  with the inner caller first the instance is filed in the caller's ring and the call compiles,
  so R007 is a by-product of filing there, not a fence for the gap.
- **Self-host status:** Curated R001/R003 parity only.
- **Status:** `bounded`: the R001, R002 and R003 clauses hold for non-generic code and, for generic
  code, under the governing meet (SR-019), with an instance filed in another ring than its caller
  refused at emission (R007, SR-018, #768); R004 and R006 are unaffected by the generic routing,
  and R004 does not reach generic free-fn calls (Known exclusions).
- **Residual risk:** None within the declared ring subset beyond the generic-call R004 gap above;
  the re-check-context asymmetry that makes the governing meet necessary is recorded as SR-019, and
  the two-ring emission index defect is closed as SR-018 (R007).

### SND-REFINE-001 [P0]

- **Claim:** Accepted refinements in the declared integer/bitvector fragment hold at checked
  construction, assignment, parameter, return, and capability-guard sinks.
- **Enforcement:** Production type-check refinement dispatchers, `z3_capability.rs`, fragment guard,
  deterministic rlimits, and fail-closed timeout/Unknown verdicts.
- **Trusted assumptions:** Z3 is correct; query encoding matches source semantics; refinements are
  preserved by every supported lowering and mutation path.
- **Independent oracle/model:** Known-answer wide-integer tests, order-independent corpus runs, and
  structural fragment-inventory tests; there is no independent formal refinement model.
- **Negative canary:** @test:u256_refinement_violating_rejected_t210 and the solver corpus fixture
  `100_refinement_guards_cap_sink.sigil`.
- **Composition coverage:** @test:wide_value_truncation_witness_t210,
  `refinement_cross_module_parity.rs`, and capability/refinement solver fixtures.
- **Known exclusions:** The grammar deliberately rejects unsupported compound, generic-function, and
  symbolic forms. The v2 pipeline is the sole production discharge path, but it is not an
  independent oracle.
- **Self-host status:** Refinements are absent from the self-hosted checker, as declared in
  `CLAIMS.md` HB-3.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence.

### SND-MEM-001 [P0]

- **Claim:** Supported array, slice, vector, arena, and host-memory accesses trap or reject rather
  than reading or writing outside their checked bounds.
- **Enforcement:** AIR/Wasm bounds checks, Wasmtime validation, runtime pointer/length validation,
  and configured memory ceilings.
- **Trusted assumptions:** Wasm emission places the guard on every access path and Wasmtime enforces
  WebAssembly memory semantics.
- **Independent oracle/model:** Runtime execution tests across independent collection and host-shim
  implementations; no formal memory model is connected to codegen.
- **Negative canary:** @test:out_of_bounds_write_traps,
  @test:get_out_of_bounds_traps_with_in_bounds_control,
  @test:rejects_alloc_i32_max_before_growing_guest_memory.
- **Composition coverage:** Collection, range-loop, arena, actor-state, and hostile-host-argument
  suites.
- **Known exclusions:** Unsafe host/native code and arbitrary Wasm outside SIGIL's verified path.
- **Self-host status:** Codegen byte-parity covers only the certified subset, not a semantic memory
  oracle; generic-enum cells are instance-sized in resolved contexts and poison otherwise.
- **Status:** `bounded`
- **Residual risk:** SR-009.

### SND-FUEL-001 [P1]

- **Claim:** Instrumented execution consumes fuel on modeled back-edges and recursion and traps when
  its runtime budget is exhausted.
- **Enforcement:** `crates/sigil-compiler/src/fuel.rs` and runtime fuel capability/state.
- **Trusted assumptions:** Lowering identifies every modeled cycle and host execution cannot bypass
  inserted checks.
- **Independent oracle/model:** Runtime state-machine properties and static worst-case-cost tests.
- **Negative canary:** @test:declared_fuel_budget_stops_an_overrunning_tool and
  @test:hostile_wasm_infinite_loop_is_bounded_by_fuel_backstop.
- **Composition coverage:** @test:nested_bounded_loops_multiply and
  @test:call_in_bounded_loop_multiplies_callee_cost.
- **Known exclusions:** Fuel is a bound/failure mechanism, not a guarantee that every accepted
  program terminates; unbounded loops have no static ceiling claim. Compile-time fuel accounting
  is narrower than the runtime's: the solver-lane QF_LIA family (`docs/z3-theory-inventory.md` §3)
  rejects only a per-site overdraw, or a negative amount, written as single-definition literals
  (a negative literal is a compile-time C002 in a solver-enabled build and a runtime signed-guard
  trap otherwise — author decision 2026-10-01); parameter and
  state-field budgets stay free and cumulative overdraw is caught only by the runtime table.
  The family is path-insensitive: a literal overdraw on a dead or conditional path rejects the
  whole function (fail-closed — it over-rejects, never under-rejects).
- **Self-host status:** Not independently modeled by the self-host checker stack.
- **Status:** `bounded`
- **Residual risk:** SR-009.

### SND-RUNTIME-001 [P0]

- **Claim:** The supported actor and forge hosts enforce their declared import, grant, capability,
  and hostile-argument behavior without silent no-ops.
- **Enforcement:** `crates/sigil-runtime/src/runtime.rs`, `ephemeral.rs`, grants, and capability table.
- **Trusted assumptions:** Deployment uses the tested Wasmtime and host configuration; behavior
  beyond the classified model-specific contracts is not inferred from registration alone.
- **Independent oracle/model:** Differential execution of equivalent actor/forge probes plus
  capability/fuel state-machine properties.
- **Negative canary:** @test:rtc_forge_traps_actor_and_cap_ops,
  @test:rtc_actor_ops_reject_hostile_args, and
  @test:declared_host_imports_really_link_and_unknown_imports_fail_closed.
- **Composition coverage:** @test:rtc_runtime_differential_census and
  @test:host_import_manifests_are_total_over_linker_registrations.
- **Known exclusions:** Behavioral actor/forge equality is asserted only for shared census probes;
  actor-only and FFI imports have model-specific contracts and tests.
- **Self-host status:** Not applicable; the runtime host is Rust.
- **Status:** `bounded`
- **Residual risk:** None for the declared import-totality boundary.

### SND-CERT-001 [P0]

- **Claim:** Certificate-gated commands do not execute when source, Wasm, schema, effects, fresh
  solver verification, or required authenticated provenance disagrees with the supplied certificate.
- **Enforcement:** `sigil-cli`/`sigil-mcp` certificate loading, re-derivation, comparison, and gate.
- **Trusted assumptions:** SHA-256 collision resistance, Ed25519 unforgeability for trusted
  release signers, canonical framing, untampered trusted command binary, and fail-closed default
  configuration.
- **Independent oracle/model:** Known-answer digest tests, signed-envelope tamper/wrong-key/replay
  tests, and separate CLI/MCP execution paths.
- **Negative canary:** @test:gate_cert_tampered_source_emits_r813,
  @test:gate_cert_tampered_wasm_emits_r814,
  @test:gate_cert_fails_closed_when_fresh_unverified_even_if_cert_claims_true,
  @test:verify_cert_rejects_cert_rebound_to_foreign_wasm,
  @test:verify_cert_refuses_wasm_binding_under_version_skew.
- **Composition coverage:** Effects under/over-grant, schema, symlink, missing, oversized, invalid
  JSON, solver-claim tamper tests, and required signed provenance. `verify-cert --wasm` binds the
  shipped module to a fresh compilation of the source (module validity, fingerprint re-derivation,
  fail-closed on compiler-version skew), never to the certificate's own fingerprint field.
- **Known exclusions:** The unsigned-local profile remains an integrity-only local workflow.
- **Self-host status:** The certified self-host emitter does not independently validate this gate.
- **Status:** `enforced`
- **Residual risk:** None for the authenticated-release certificate provenance profile.

### SND-FRONTEND-001 [P0]

- **Claim:** A supported foreign frontend either emits SIGIL inside its documented subset and passes
  the production compiler under `FFC-2026-09-07`, or rejects the input without silently dropping
  security-relevant syntax.
- **Enforcement:** Frontend-specific allow-list parsers/checkers followed by SIGIL compilation and
  the drift-pinned `correspondence_profile.rs` gate.
- **Trusted assumptions:** The versioned correspondence profile is the authority for the accepted
  source grammar; behavior outside that profile remains excluded.
- **Independent oracle/model:** Hand-authored golden emission, round-trip compilation, deterministic
  translation, adversarial corpora, dev-only Rust parser agreement, Solidity property lowerings, and
  an independently implemented finite scalar-expression oracle for all shipped frontends.
- **Negative canary:** @test:reject_fixtures_match_expected_codes and frontend depth/unsupported
  construct tests.
- **Composition coverage:** Solidity inheritance/modifier/ERC20 adversarial suites and Rust/TypeScript
  security-policy enforcement fixtures.
- **Known exclusions:** Anything outside each frontend's explicit subset; no claim is made that the
  whole source language is equivalent to SIGIL.
- **Self-host status:** Self-hosted SIGIL front-end tests validate emitted SIGIL only where the
  downstream differential corpus reaches it.
- **Status:** `enforced`
- **Residual risk:** None for `FFC-2026-09-07`.

### SND-SELFHOST-001 [P1]

- **Claim:** Self-hosted components agree with the Rust oracle only on each differential suite's
  declared corpus and projection.
- **Enforcement:** Differential suites for lexer, parser, name resolution, type checking, ring,
  effect, taint, ownership, capability workloads/verdicts, AIR, monomorphization, and emit bytes.
- **Trusted assumptions:** Corpus generation is non-vacuous, projections preserve distinguishing
  information, and both sides do not share the same bug or parser loss.
- **Independent oracle/model:** Rust and SIGIL implementations are structurally diverse but share
  specifications and some lowering assumptions.
- **Negative canary:** Per-suite non-stub, deterministic, reject/accept, and anti-vacuity tests;
  @test:ag6_7_unresolved_generic_enum_contexts_fail_closed fences unsupported enum contexts, and
  @test:boot1_unsupported_taint_shape_fails_closed fences unsupported taint contexts.
- **Composition coverage:** Certified byte capstones and whole-stdlib floors where the Rust oracle can
  process the same input; @test:ag6_6_narrow_variant_size_corpus covers generic enum construction
  across annotations, returns, calls, and multiple type parameters;
  @test:hb2_checked_byte_capstone runs the seven-gate chain over the certified artifact itself.
- **Known exclusions:** These are curated relations, not full-language equivalence; the executed gate
  chain enforces only each gate's parity-covered code subset, and the with-driver artifact's own
  driver still runs the emit lane rather than the gates.
- **Self-host status:** This row describes the bounded status itself.
- **Status:** `bounded`
- **Residual risk:** SR-009.

### SND-FORMAL-001 [P1]

- **Claim:** The production model-9 verifier first validates and re-verifies the exact retained
  version-8 Combined CSIR prefix, then derives occurrence policy from canonical v9 host, actor,
  FFI, and function-root declarations. The retained prefix contains a resolved AIR envelope:
  its manifest counts, functions, typed SSA values, blocks, instructions, contiguous operands,
  destinations, arities, function references, and same-function CFG targets. Declarative v8
  metadata supplies label/flow contracts, capability types, policy classes, refinement facts, and
  guard declarations without carrying Rust-computed security verdicts. The verifier directly
  derives least semantic SSA/CFG taint and pc-taint over security-only SSA versions and
  predecessor-compressed phi instructions, restores structured pc-taint at branch/loop merge
  points, excludes type-proved unreachable exhaustive-match fallthroughs, and checks contracts,
  state/output flows,
  releases, T020--T029/T031--T033 observations, assignment/return/call/state-result T030 CT sources, Public
  quantity operands, guard presence, and local capability
  type/attenuation shapes. Its retained v6 obligation families also derive taint and pc-taint from bounded seeds and
  monotone edges (including cyclic loop back-edges), then checks sinks, two-stage releases, and
  SecretCT uses. It also derives capability legitimacy and BV32 authority through
  restrict/split/draw, control-flow meet, slot put/take meet, sinks, and release gates. Explicit
  `if`/`match` branch markers drive a fallthrough-aware path-affine consumption judgment; loop
  markers reject carried-origin consumption on repeatable edges and join `break` consumption into
  the exit. Signed quantity cells, normalized difference constraints, mandatory guest/host guards,
  and Public-only amount sinks are part of the same verdict. A
  successful compilation carries the report returned by that exact linked Lean function.
- **Enforcement:** exhaustive typed-obligation and post-desugar AIR projections in
  `formal::verify_with_context` at the shared compiler choke point, the statically linked
  `OccurrenceKernel.exportedVerify` (which runs the retained semantic/Combined decision first),
  exact model-9 CSIR/report hashing, schema-v9 fresh re-derivation and R819 comparison, host-profile
  Wasm binding before instantiation, exact Rust/Lean opcode parity,
  compiler-output parity manifest, exported-tree proof/evidence gates, the Lean no-sorry/axiom gate,
  and the versioned [`PLC-2026-09-07`](specs/production-lean-composition.md) composition profile.
- **Trusted assumptions:** Rust source-to-CSIR projection, the pinned Lean kernel/toolchain, Lean
  C/native generation and runtime, Wasm/runtime/platform behavior, and the theorem statement/CSIR
  model remain assumptions tracked by SR-017.
- **Independent oracle/model:** Existing Rust taint/ownership and AIR capability gates remain
  mandatory differential oracles under `PLC-2026-09-07` and through the first dual-gate release.
- **Negative canary:** @test:planted_bad_authority_is_rejected_by_linked_lean,
  @test:linked_lean_derives_transitive_taint_instead_of_trusting_a_sink_label,
  @test:linked_lean_derives_bv32_attenuation_instead_of_trusting_a_mask,
  @test:linked_lean_rejects_a_capability_derivation_without_a_legitimate_origin,
  @test:linked_lean_slot_take_uses_the_meet_of_put_authorities,
  @test:linked_lean_accepts_a_guarded_empty_slot_take,
  @test:linked_lean_empty_slot_take_still_enforces_the_ceiling,
  @test:slot_take_on_empty_traps_unreachable,
  @test:linked_lean_rejects_two_consumptions_on_one_path,
  @test:linked_lean_rejects_use_after_a_may_consume_join,
  @test:linked_lean_rejects_consuming_a_loop_head_capability_on_a_back_edge,
  @test:linked_lean_carries_break_consumption_to_the_loop_exit,
  @test:linked_lean_rejects_wrong_v8_semantic_constructor_count,
  @test:linked_lean_rejects_noncanonical_v8_semantic_metadata,
  @test:linked_lean_rejects_v8_block_without_a_terminator,
  @test:linked_lean_rejects_v8_reordered_owner_records,
  @test:linked_lean_rejects_v8_reordered_sibling_values,
  @test:linked_lean_rejects_v8_reordered_sibling_blocks,
  @test:linked_lean_rejects_v8_terminator_destination,
  @test:linked_lean_rejects_v8_wrong_operand_order,
  @test:linked_lean_rejects_v8_cap_restrict_without_mask,
  @test:linked_lean_rejects_v8_cap_restrict_over_copy_values,
  @test:linked_lean_rejects_noncontiguous_v8_operand_slice,
  @test:linked_lean_rejects_missing_v8_cfg_target,
  @test:linked_lean_rejects_v8_without_a_semantic_manifest,
  @test:rust_and_lean_wire_opcode_tables_are_identical,
  @test:linked_lean_enforces_direct_t030_ct_source_policy,
  @test:package_certificate_nested_unknown_fields_fail_closed,
  @test:parity_manifest_matches_the_committed_rows,
  @test:selfhost_trio_completes_within_validation_budget,
  @test:lean_kernel_caches_whole_program_indexes_outside_inner_loops,
  @test:linked_lean_indexes_large_single_function_without_nested_copying,
  @test:ci_keeps_formal_verifier_scaling_canary,
  @test:if_divergent_guard_clause_compiles,
  @test:two_thousand_sibling_ifs_compile,
  @test:two_thousand_sibling_whiles_compile,
  @test:two_thousand_sibling_matches_compile,
  @test:declaration_success_does_not_authorize_an_occurrence_boundary_violation,
  @test:production_v9_rejects_actor_send_in_secret_loop_header,
  @test:production_v9_preserves_the_pure_secret_loop_header_twin,
  @test:production_v9_enforces_actual_ffi_arguments_against_the_bound_profile,
  @test:gate_cert_rejects_changed_host_occurrence_metadata_as_r819,
  @thm:Combined.wrong_instruction_arity_mutant_rejects,
  @thm:Combined.missing_semantic_dispatch_policy_rejects,
  @thm:Combined.policy_on_unconditional_jump_rejects,
  @thm:Combined.missing_ct_source_policy_rejects,
  @thm:Combined.internal_ct_source_rejects_t030,
  @thm:Combined.loop_backedge_taint_rejects,
  @thm:Combined.missing_pc_join_mutant_readmits_violation,
  @thm:Combined.structured_pc_restore_accepts,
  @thm:Combined.missing_structured_pc_restore_rejects,
  @thm:Combined.secret_closure_selector_taints_every_callee_entry,
  @thm:Combined.direct_call_only_mutant_omits_the_dynamic_callee_edge,
  @test:linked_lean_rejects_malformed_input,
  @test:gate_cert_missing_formal_report_emits_r819,
  @test:gate_cert_tampered_csir_fingerprint_emits_r819,
  @test:production_lean_composition_profile_is_complete_and_drift_pinned, and
  @test:production_lean_composition_profile_keeps_public_claims_bounded.
- **Composition coverage:** `PLC-2026-09-07` machine-checks the production abstraction relation,
  public theorem names, positive and negative canaries, and mandatory gate tokens for every
  production-facing checker-composition obligation. @thm:Combined.graph_verifier_sound_and_complete equates executable graph
  acceptance with the per-node bounded-reference and derived-label judgment; every accepted edge is checked
  as a post-fixed-point constraint. @thm:Combined.graphLabels_least proves the linked worklist is
  below every algorithm-independent seed/edge solution, so accepted output is the least solution.
  @thm:Combined.joint_security_of_verified proves the conjunction over the remaining decoded
  obligations and exposes that least-solution characterization.
- **V9 occurrence composition:**
  @thm:Combined.V9.OccurrenceKernelSecurity.v9_occurrence_verifier_sound_and_complete reflects the
  exact executable decision into its instruction-indexed unary judgment. Returned analysis carries
  least semantic labels, the ranked transfer postcheck and closed invocation graph. Effective
  occurrence is checked at every destination, actual FFI argument and FFI occurrence boundary;
  state-write ceilings come from the owning function's declaration, all raw-observable actor
  subtypes remain Public, and root return occurrence is keyed by the stable root contract. This
  unary result does not by itself claim activation-aware raw execution; the downstream Public
  composition below supplies that connection.
- **Raw relational composition (SecretCT and Public connected):**
  @thm:Combined.v8_semantic_verifier_sound_and_complete connects the executable semantic decision
  to `V8SecurityJudgment`. The unsanitized semantic machine proves constructor-complete
  preservation through @thm:Combined.Semantic.state_well_formed_preserved and conditional SecretCT
  lockstep/delimited-release through @thm:Combined.Semantic.raw_secretCT_step_lockstep_of_static_safe and
  @thm:Combined.Semantic.raw_secretCT_delimited_release_trace_equality_of_static_safe. Releases compare
  exact site, stage, and payload at every prefix.
  @thm:Combined.raw_secretCT_static_safe_of_v8_verified connects linked acceptance to that decoded
  premise, and @thm:Combined.RawClaimSurface.secretCT_delimited_release_trace_equality is the
  production-facing corollary. Its complete transitive declaration closure is CI-audited against
  sanitized and assumed-policy symbols with a planted failing dependency. The linked decoded
  decision now rejects a non-Public control arm that can `output` or `halt` before a derived Public
  continuation. Only a flat-match wrapper exit restores pc-taint; an inner arm-test else target
  does not. @thm:Combined.secret_arm_successful_escape_breaks_the_public_path_check is the
  theorem-breaking path mutant, with linked-native direct-arm and catch-all escape cases in the
  Rust suite. Unreachable AIR
  is projected to a trap, and decoded halt acceptance additionally requires a verifier-derived
  Public block label. @thm:Combined.non_public_callee_halt_mutant_rejects and the linked secret-arm
  callee fixture pin the interprocedural escape that a caller-only path walk would miss.
  @thm:Combined.V9.PublicBisimulationSecurity.raw_public_weak_bisimulation_of_v9_verified derives
  a finite weak alignment from production v9 acceptance, matching verified Public cut points,
  full Public-low equivalence, two independently sized successful executions, immutable equal
  per-site external-input streams, and equality of the complete release traces. Calls, closures,
  recursive activations, unequal private branch/loop lengths, genuine returns, and multiple
  releases are handled by verifier-derived matching and private-segment cases. No alignment,
  merge certificate, or relational policy is supplied by the caller. The pinned
  @thm:Combined.RawClaimSurface.public_delimited_release_noninterference corollary concludes
  equality of every component of `publicProjection` and the ordered Public output/boundary trace
  for separate successful-run fuel budgets. Its transitive declaration closure is fingerprinted
  and CI-audited alongside the SecretCT claim.
- **Capability composition:** @thm:Combined.capability_verifier_sound_and_complete equates executable
  capability acceptance with the ordered derivation judgment over verifier-produced states;
  @thm:Combined.capability_restriction_rejects_missing_authority and
  @thm:Combined.slot_authority_meet_rejects are non-vacuous witnesses.
  @thm:Combined.empty_slot_take_accepts_guarded_continuation and
  @thm:Combined.empty_slot_take_still_enforces_authority_ceiling pin the guarded-trap abstraction.
- **Affine composition:** @thm:Combined.path_affine_verifier_sound_and_complete equates the
  executable branch-state machine with its ordered judgment;
  @thm:Combined.alternative_path_consumption_accepts and
  @thm:Combined.use_after_may_consume_join_rejects are non-vacuous branch twins;
  @thm:Combined.loop_backedge_consumption_rejects,
  @thm:Combined.single_break_consumption_accepts, and
  @thm:Combined.use_after_break_consumption_rejects cover loop repetition and exits.
- **Difference-classifier coverage:** The executable classifier is sound and complete for the exact
  version-6 literal-RHS fragment: every normalized edge is zero-anchored, every referenced cell
  carries implicit i64 bounds, and canonical record IDs keep references in bounds.
  `@thm:Combined.difference_classifier_sound_and_complete_of_nodes` derives those premises from
  the verifier's quantitative node checks; `@thm:Combined.unsupported_cross_cell_constraint_rejects`
  pins the fail-closed boundary. Arbitrary cell-to-cell difference graphs are not a supported or
  claimed v6 feature.
- **AIR transfer correspondence:** APC-1 checks local definition/use renaming and independently
  enumerated predecessor transfers against emitted CSIR. The production-linked
  @thm:Combined.Projection.accepted_bytes_preserve_paths preserves every extracted finite transfer
  path through actual phi operands. @test:projection_accepts_source_branches_loops_and_reordered_blocks,
  @test:projection_rejects_missing_branch_and_backedge_inputs_even_when_plan_agrees, and
  @test:projection_native_checker_rejects_mutated_phi_records_and_witnesses exercise the boundary.
  Extraction completeness, unreachable-path justification, opcode/metadata semantics, and
  local-read serialization remain assumptions; the generic rank corollary requires phi closure.
- **Known exclusions:** The resolved raw semantic machine uses the same closed instruction
  vocabulary as production v8. Its SecretCT finite-prefix result is a corollary of executable
  verifier acceptance; its Public independent-length result is a production-linked corollary of
  model-9 acceptance. The Public result deliberately does not equate ordinary-Secret timing,
  control, address, allocation, or cost traces. `PLC-2026-09-07` relates the shipped checker
  transitions, retained-v6 compatibility layer, Lean theorems, and executable canaries for the
  current CSIR verifier stack, but it is not a source/AIR/Wasm adequacy proof. Rust source-to-CSIR
  projection, including security-only SSA versioning, phi placement, and type-proved unreachable
  fallthrough projection, remains trusted. Lean native generation/runtime, Wasm emission, Wasmtime,
  scheduling/queues, microarchitecture, hardware timing, platform release evidence, and old-gate
  retirement are SR-017. Local accepted-corpus parity is green, including the committed JSON
  library; the deliberate Wasm export correction is pinned in the regenerated parity manifest. The
  v9 dual-gate evidence remains non-retirement-eligible.
- **Self-host status:** Separate differential evidence source.
- **Status:** `enforced`
- **Residual risk:** None for `PLC-2026-09-07`; SR-017 remains open for source-to-CSIR,
  post-CSIR runtime/lowering, platform, performance, and old-gate retirement adequacy.

### SND-DIAG-001 [P1]

- **Claim:** Security diagnostic registrations cannot silently lose their production reference or
  disappear from the measured test/self-host evidence surface without changing a pinned census.
- **Enforcement:** `diagnostics::registry::CODES`, the diagnostic coverage manifests, and
  `soundness_contract.rs`.
- **Trusted assumptions:** A static code reference is an anti-deletion signal, not proof that its
  branch is reachable; fixture execution and semantic tests remain separate evidence.
- **Independent oracle/model:** Registry snapshot/doc generation and executable fixture wiring use
  separate inventories and checks.
- **Negative canary:** @test:diagnostic_security_surface_is_censused.
- **Composition coverage:** @test:registry_codes_have_fixtures and
  @test:diagnostic_code_list_matches_golden cover active fixture emission and public-code stability.
- **Known exclusions:** 65 security codes lack a direct Rust/SIGIL test reference, and only 28 are
  represented in self-host output; both numbers are explicit and pinned, not parity claims.
- **Self-host status:** A measured 28-code subset across the declared checker projections.
- **Status:** `bounded`
- **Residual risk:** None for census drift; semantic gaps remain listed in
  `diagnostic-test-gaps.txt`.
