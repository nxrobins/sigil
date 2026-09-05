# Sigil Attack Matrix

**67 attack programs. 15/15 tournament vectors defended. 0 gaps.**

Phase 2H (Constant-Time, `@SecretCT`) ships 13 net-new attacks:
CT001–CT007 + CT010–CT017 (CT008/CT009 spec-reserved, no current
language surface for variable shifts or short-circuit boolean operators).
Spec name ↔ diagnostic code mapping in `docs/specs/secret-ct.md`.

135 tests total across workspace (54 prior attacks + 81 positive/
structural/integration) plus Phase 2H additions (13 + 9 + 2 = 24 new
CT tests). 102 compiler + 24 runtime + 5 registry + 4 CLI harness +
Phase 2H test files.

> **Companion documents:** [`CVE-MATRIX.md`](CVE-MATRIX.md) — the CVE
> retrofit corpus showing SIGIL's response to 10 famous publicly-disclosed
> CVEs (Log4Shell, The DAO, Spring4Shell, Citrix path traversal, etc.);
> [`PERFORMANCE.md`](PERFORMANCE.md) — measured compile-throughput +
> Wasm-size numbers; [`COMPARISON.md`](COMPARISON.md) — SIGIL vs Pony /
> Rust / Joe-E / Erlang / Caja at the feature level with primary-source
> citations.
> Where this document tracks SIGIL's internal adversarial corpus, the
> CVE matrix tracks SIGIL versus real-world bug shapes.

> **Diagnostic codes**: every error code referenced in this document
> (`T001`, `R001`, `O001`, `E001`, `C001`, `F001`, etc.) has a stable entry in
> [`docs/ERROR-CODES.md`](docs/ERROR-CODES.md) with a title and a fix recipe.
> The Sigil compiler emits these codes via the structured JSON diagnostic
> wire format (`sigil check --json`).

---

## Tournament Vector Coverage

| Vector | Attacks | Defense Layers | Status |
|--------|---------|----------------|--------|
| capability_escalation | #04, #06, #08, #43 | Type, Z3 bitvectors, Ownership | ✅ |
| cross_boundary_read | #09, #41, #47 | Wasm TrapIf, Memory isolation, Import segregation | ✅ |
| cross_boundary_write | #09, #10, #47 | Wasm TrapIf, Unsigned bounds, Import segregation | ✅ |
| unbounded_allocation | #12 | Fuel exhaustion | ✅ |
| unbounded_execution | #12, #13 | Fuel exhaustion, Stack depth | ✅ |
| network_exfiltration | #18, #34, #36, #37 | Ring R003, Effect E001, Type F001 | ✅ |
| filesystem_escape | #06 | Z3 authority bitvectors | ✅ |
| serialization_injection | #04, #38 | Type checker, FFI taint @Internal | ✅ |
| error_oracle | #20, #38 | Ring R005 ErrorCode, FFI taint @Internal | ✅ |
| concurrency_corruption | #01, #02, #05 | Ownership (move-on-send) | ✅ |
| audit_evasion | #42 | Ring boundary (grants required + logged) | ✅ |
| identity_forgery | #04 | Type checker (ActorRef unforgeable) | ✅ |
| delegation_escalation | #06, #08, #43 | Z3 bvule, Spawn verification, Generics | ✅ |
| eval_injection | — | By construction (no eval, no dynamic code) | ✅ |
| covert_timing_channel (algorithmic) | CT001–CT017 | Taint checker (CT pass), closure propagation, source-of-CT, declassify_ct chain | ✅ |
| covert_timing_channel (microarchitectural) | — | Out of scope per spec §9.1; requires CPU/OS/hardware mitigation | ⚠️ Anti-goal |

---

## Full Attack Inventory

### Phase 1 — Core Language (14 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 01 | Use-after-move | Ownership checker | O001 | reject |
| 02 | Loop double-spend | Ownership checker | O001 | reject |
| 03 | Sealed vault reassignment | Type membrane | Type error | reject |
| 04 | Capability forgery | Type checker | C001 | reject |
| 05 | Ask double-spend | Ownership checker | O001 | reject |
| 06 | Escalation via aliasing | Z3 bitvectors | C003 | reject |
| 07 | Fuel counterfeit | Runtime fuel system | Trap | runtime |
| 08 | Spawn cap mismatch | Z3 verification | C001 | reject |
| 09 | Heap smash (OOB write) | Wasm TrapIf | Trap | runtime |
| 10 | Negative index alias | Unsigned I32GeU | Trap | runtime |
| 11 | Empty array ICE | Type checker | Type error | reject |
| 12 | Infinite loop | Fuel exhaustion | Trap | runtime |
| 13 | Deep recursion | Fuel/stack limit | Trap | runtime |
| 14 | Supervisor contamination | Restart supervision | Runtime | runtime |

### Phase 2B — Ring System (8 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 15 | Outer ring holds cap | Ring checker | R001 | reject |
| 16 | Outer ring defines actor | Ring checker | R001 | reject |
| 17 | Cap ref escapes grant | Ring checker | R002 | reject |
| 18 | Inner calls extern | Ring checker | R003 | reject |
| 19 | Direct cross-ring call (inner→outer) | Ring checker | R004 | reject |
| 19b | Direct cross-ring call (outer→inner) | Ring checker | R004 | reject |
| 20 | Rich error across boundary | Ring checker | R005 | reject |
| 21 | Grant cap ref in message | Ownership | O007 | reject |
| 22 | Cap moved while grant active | Ownership | O007 | reject |

### Phase 2C — Effect System (6 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 23 | Pure fn calls effectful fn | Effect checker | E001 | reject |
| 24 | Missing effect in row | Effect checker | E001 | reject |
| 25 | handle Unsafe in untrusted module | Effect checker | E002 | reject |
| 26 | Outer fn missing effect clause | Effect checker | E001 | reject |
| 27 | Inner fn with ! clause | Effect checker | E003 | reject |
| 28 | Closure with undeclared effects | Effect checker | E001 | reject |

### Phase 2D — Taint System (5 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 29 | @Secret to @Public sink | Taint checker | T001 | reject |
| 30 | Implicit flow (branch on secret) | Taint checker | T001 | reject |
| 31 | @Secret through grant return | Taint checker | T001 | reject |
| 32 | @Public + @Secret concat to sink | Taint checker | T001 | reject |
| 33 | Declassify cap reused | Ownership | O001 | reject |

### Phase 2E — FFI and Regions (5 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 34 | Inner ring extern declaration | Ring checker | R003 | reject |
| 35 | handle Unsafe in non-trusted | Effect checker | E002 | reject |
| 36 | Extern call outside handle block | Effect checker | E001 | reject |
| 37 | Ptr<T> outside extern context | Type checker | F001 | reject |
| 38 | FFI return @Internal to @Public | Taint checker | T001 | reject |
| 39 | Region reference escape | Ownership | O006 | reject |

### Phase 2F — Two-Module Codegen (2 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 40 | Outer module has no cap imports | Import segregation | Structural | structural |
| 41 | Outer module memory isolation | Wasm sandbox | Structural | structural |

### Phase 2G — Cross-Cutting Validation (6 attacks)

| # | Attack | Defense | Error | Type |
|---|--------|---------|-------|------|
| 42 | Audit evasion | Ring boundary + grant logging | Structural | structural |
| 43 | Generic cap smuggle | Ownership through monomorphization | O001 | reject |
| 44 | Closure cap capture + grant escape | Borrow checker | O006 | reject |
| 45 | Effect row smuggle via closure | Effect checker | E001 | reject |
| 46 | Taint launder via declassify loop | Ownership (linear cap) | O001 | reject |
| 47 | Two-ring import segregation | Wasm import section | Structural | structural |

### Phase 2H — Constant-Time (`@SecretCT`) (13 attacks)

See `docs/specs/secret-ct.md` for the full discipline. Algorithmic
timing only; microarchitectural channels (Spectre, cache, SMT, EM/
power) are explicit anti-goal per spec §9.1. Spec names CT001–CT017
map to diagnostic codes T020–T032 (with O001 for CT011 cap-reuse).

| #  | Attack | Defense | Error | Type |
|----|--------|---------|-------|------|
| CT001 | `if` branch on `@SecretCT` condition | Taint checker (CT pass) | T020 | reject |
| CT002 | `while` loop on `@SecretCT` condition | Taint checker (CT pass) | T021 | reject |
| CT003 | `for x in iter` with `@SecretCT` iterable | Taint checker (CT pass) | T022 | reject |
| CT004 | `match` on `@SecretCT` scrutinee | Taint checker (CT pass) | T023 | reject |
| CT005 | array index by `@SecretCT` | Taint checker (CT pass) | T024 | reject |
| CT006 | `load8` / `store8` at `@SecretCT` address | Taint checker (CT pass) | T025 | reject |
| CT007 | `div` with `@SecretCT` operand | Taint checker (CT pass) | T026 | reject |
| CT008 | variable shift by `@SecretCT` | Spec-reserved (no `Shl`/`Shr` BinaryOp in language) | — | reserved |
| CT009 | short-circuit `&&` / `\|\|` on `@SecretCT` | Spec-reserved (no short-circuit operator in language) | — | reserved |
| CT010 | `@SecretCT` passed to extern fn | Taint checker (CT pass) | T027 | reject |
| CT011 | `declassify_ct` cap reuse | Ownership (linear cap) | O001 | reject |
| CT012 | `@SecretCT` smuggled via closure capture | Closure CT propagation (§3.7) → CT001–CT017 | T020–T031 | reject |
| CT013 | `@SecretCT` smuggled via generic monomorphization | Monomorphization preserves taint → CT001–CT017 | T020–T031 | reject |
| CT014 | `@SecretCT` payload to `send` / `ask` | Taint checker (CT pass) | T028 | reject |
| CT015 | `alloc(n)` / `region(n)` with `@SecretCT` size | Taint checker (CT pass) | T029 | reject |
| CT016 | `@Internal` / `@Secret` → `@SecretCT` upcast | Taint checker (source-of-CT, E1) | T030 | reject |
| CT017 | `declassify` of `@SecretCT` input | Taint checker (declassify input contract, E2) | T031 | reject |
| CT-AUDIT | Codegen regression introduces forbidden opcode | Wasm byte-scan in `tests/taint_ct_audit.rs` (§10.16) | panic | regression-guard |

---

## Defense Layer Summary

| Layer | Pass | Attacks Defended | Phase |
|-------|------|-----------------|-------|
| Type checker | type_check.rs | #03, #04, #08, #11, #37 | 1, 2E |
| Ownership checker | ownership.rs | #01, #02, #05, #21, #22, #33, #39, #43, #44, #46, CT011 | 1, 2A, 2G, 2H |
| Z3 bitvectors | z3_capability.rs | #06, #08 | 2A |
| Ring checker | ring_check.rs | #15, #16, #17, #18, #19, #19b, #20, #34 | 2B |
| Effect checker | effect_check.rs | #23, #24, #25, #26, #27, #28, #35, #36, #45 | 2C, 2G |
| Taint checker | taint_check.rs | #29, #30, #31, #32, #38, CT001–CT007, CT010, CT012–CT017 | 2D, 2H |
| Wasm sandbox | wasm.rs | #09, #10, #40, #41, #47 | 1, 2F |
| Wasm byte-scan audit | tests/taint_ct_audit.rs | CT-AUDIT | 2H |
| Fuel system | fuel.rs + runtime | #07, #12, #13 | 1 |
| Runtime | sigil-runtime | #14, #42 | 1, 2G |

---

## Residual Risks

| Risk | Status | Mitigation |
|------|--------|------------|
| Algorithmic timing channel | Defended (Phase 2H) | `@SecretCT` typecheck (CT001–CT017) + Wasm byte-scan audit |
| Microarchitectural side channels (Spectre, cache, SMT, EM/power) | Anti-goal (spec §9.1) | Out of scope; requires CPU/OS/hardware mitigation |
| Trap-timing observability (fuel exhaustion in CT scope) | Documented (spec §9.2) | Callers MUST size fuel from public inputs only |
| Non-CT helper transitive timing | Anti-goal (spec §9.3) | CT scope is per-function signature, not transitive call graph |
| Audit log tampering | Mitigated | Audit log in host memory, unreachable from Wasm |
| Runtime bugs | Mitigated | Two-module isolation (2F), defense-in-depth |

---

*Updated for Phase 2H Constant-Time validation. 67 attacks across 9 phases, 15/15 tournament vectors.*
