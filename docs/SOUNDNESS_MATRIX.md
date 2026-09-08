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
- **Trusted assumptions:** Typed-AST labels and actor signatures are correct; all relevant typed
  expression and statement variants are visited; runtime behavior preserves the checked boundary.
- **Independent oracle/model:** The Lean taint calculus proves its own trace property;
  `selfhost/taint_check.sigil` differentially covers a curated scalar/record/closure subset.
- **Negative canary:** @test:implicit_flow_secret_guarded_break_leak,
  @test:direct_call_rejects_secret_into_public_parameter,
  @test:abortive_effect_clause_preserves_secret_parameter_taint,
  @test:legacy_handle_checks_every_nested_statement,
  @test:extern_call_rejects_secret_argument, @test:spawn_secret_cap_into_public_init_is_rejected,
  and @test:every_wrong_generic_call_arity_is_i013_not_an_abort.
- **Composition coverage:** @test:while_continue_skips_reset_is_rejected,
  @test:continue_inside_match_arm_in_loop_is_rejected, @test:break_bypasses_declassify_barrier,
  @test:indirect_call_rejects_non_public_argument_without_taint_contract,
  @test:abortive_effect_clause_checks_every_nested_statement, and
  @test:region_checks_every_nested_statement. @test:malformed_partial_typed_call_fails_closed_in_taint
  pins the public recovery interface, while
  @test:taint_checker_source_has_no_release_abort_primitives prevents release-abort primitives
  from returning to the taint pass.
- **Known exclusions:** Termination observation, environmental side channels, heap-content precision,
  and arbitrary foreign behavior. Higher-order function types do not encode taint contracts, so
  non-Public indirect-call arguments are conservatively rejected. Conservative false rejects are permitted.
- **Self-host status:** Curated parity only. Control joins, early-exit continuation taint, match
  guards, actor/spawn boundaries, and closure-value taint emit an explicit unsupported verdict,
  which the composed self-host pipeline rejects.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence.

### SND-CT-001 [P0]

- **Claim:** `SecretCT` cannot drive supported source-level variable-time control, address,
  division, FFI, actor-boundary, or allocation operations.
- **Enforcement:** `crates/sigil-compiler/src/taint_check.rs` emits T020-T032;
  `crates/sigil-compiler/tests/taint_ct_audit.rs` checks emitted Wasm patterns.
- **Trusted assumptions:** The source-to-Wasm lowering preserves the audited operation classes and
  host imports do not add secret-dependent behavior.
- **Independent oracle/model:** Curated self-host T-code parity plus a separate Wasm byte audit.
- **Negative canary:** @test:ct001_if_on_secret_ct_rejected,
  @test:ct002_while_guard_tainted_inside_loop_rejected, @test:ct005_index_by_secret_ct_rejected,
  @test:closure_parameter_taint_is_enforced_inside_body,
  @test:direct_call_rejects_non_ct_secret_into_secretct_parameter,
  @test:spawn_secretct_cap_is_rejected_t028.
- **Composition coverage:** @test:ct012_closure_capturing_secret_ct_branch_rejected and the
  `taint_constant_time_phase_b` generic/closure corpus.
- **Known exclusions:** Microarchitectural, OS, host, speculative, cache, power, and EM channels.
- **Self-host status:** Curated T020-T032 parity; actor and unsupported control distinctions reject
  explicitly rather than widening the parity claim.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence.

### SND-CAP-001 [P0]

- **Claim:** Source cannot forge capability authority, and authority delivered to a checked
  call/spawn/send/return sink must satisfy the sink obligation.
- **Enforcement:** Type construction membrane, `crates/sigil-compiler/src/air_capability_v2`, and
  runtime capability tables.
- **Trusted assumptions:** Authority registries assign stable bits; capability lowering identifies
  every sink; Z3 answers only inside the guarded fragment.
- **Independent oracle/model:** Lean capability calculus, self-hosted pure-workload/verdict shadow,
  and runtime capability-table state-machine properties.
- **Negative canary:** @test:the_sole_prover_rejects_every_capability_rejection_fixture,
  @test:cap_forgery_rejected_by_frontend.
- **Composition coverage:** `cap_aggregate_smuggle.rs`, `ring_cap_aggregate_smuggle.rs`,
  @test:cap3_reject_matches_oracle, and @test:cap_sink_contract_is_deliberately_full_mask cover
  generics, aggregates, rings, all sink kinds, and the conservative body-independent contract.
- **Known exclusions:** At most 32 authority bits; capability parameters cannot declare a reduced
  authority subset; Lean does not model the full `mintable_by` policy.
- **Self-host status:** Pure workload and verdict parity on a curated cap-only subset.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence.

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
  introduce an unchecked operation after the security walk.
- **Independent oracle/model:** `selfhost/effect_check.sigil` parity for E001/E002 and Lean
  `effect_safety` (synthesized rows) plus the `Chk` checking judgment
  (`Chk.effect_safety_declared`, `Chk.app_latent_bounded` in `EffectRows.lean`) for declared-row
  and latent-row containment.
- **Negative canary:** @test:sh_effect_reject_matches_oracle and effect-handler E004 residue tests.
- **Composition coverage:** @test:sh_effect_stdlib_clean_parity_and_floor plus
  `generic_impl_effects.rs` and `effect_handlers.rs`.
- **Known exclusions:** the Lean⇄Rust relation is a reviewed correspondence, not a mechanized
  bridge; generic call-site instantiation binding is a trusted assumption; the self-host shadow
  covers E001/E002, not the full handler diagnostic surface.
- **Self-host status:** Curated E001/E002 parity and a stdlib clean floor.
- **Status:** `bounded`
- **Residual risk:** SR-017 for stronger source-to-runtime correspondence.

### SND-RING-001 [P1]

- **Claim:** Outer-ring code cannot own capabilities and inner-ring code cannot directly exercise
  foreign authority outside the declared crossing rules.
- **Enforcement:** `crates/sigil-compiler/src/ring_check.rs`, type-check crossing rules, and
  ring-specific Wasm memories/import sets.
- **Trusted assumptions:** Every module/function has the correct ring and the emitted import/memory
  partition matches the checked program.
- **Independent oracle/model:** `selfhost/ring_check.sigil` differential parity on R001/R003 and
  runtime host/import tests.
- **Negative canary:** @test:sh_ring_reject_matches_oracle.
- **Composition coverage:** `ring_cap_aggregate_smuggle.rs` and runtime host-boundary tests.
- **Known exclusions:** R002 is pre-empted by a type error in the differential corpus; R004 is
  enforced outside the ring shadow.
- **Self-host status:** Curated R001/R003 parity only.
- **Status:** `bounded`
- **Residual risk:** None within the declared ring subset.

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
  program terminates; unbounded loops have no static ceiling claim.
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
  @test:gate_cert_fails_closed_when_fresh_unverified_even_if_cert_claims_true.
- **Composition coverage:** Effects under/over-grant, schema, symlink, missing, oversized, invalid
  JSON, solver-claim tamper tests, and required signed provenance.
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
