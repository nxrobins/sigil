# `@SecretCT` Constant-Time Information Flow

**Status:** Implemented for the algorithmic source and Wasm surface described
below.

`@SecretCT` is the top of SIGIL's information-flow lattice:

```text
@Public < @Internal < @Secret < @SecretCT
```

Ordinary taint tracking prevents confidential values from reaching lower
sinks. `@SecretCT` adds an opt-in operational rule: accepted source must not
let CT-labeled data select supported control flow, memory addresses,
variable-time arithmetic, or observable boundaries.

The authoritative security boundary is
[`../SECURITY_MODEL.md`](../SECURITY_MODEL.md). This document defines the
constant-time subset in detail.

## 1. Guarantee

For supported SIGIL constructs, the compiler rejects an operation when an
`@SecretCT` value controls:

- branch or dispatch selection;
- loop trip count;
- a memory index or address;
- division;
- foreign, actor, or allocation boundaries whose behavior is opaque or
  externally observable.

The guarantee is algorithmic. It concerns source-level operation classes and
the direct Wasm emitted for SIGIL's CT intrinsics. It is not a claim about
microarchitectural or environmental constant time.

`@SecretCT` is a separate label instead of making all `@Secret` values CT.
That keeps the existing confidentiality policy compatible while allowing
cryptographic and timing-sensitive code to request the stricter discipline.

## 2. Sources and flow

The ordinary lattice permits upward flow, but an additional source check
controls construction of `@SecretCT` values:

- `@Public -> @SecretCT` is allowed for public constants, masks, and inputs
  that carry no secret provenance.
- `@SecretCT -> @SecretCT` is allowed.
- `@Internal -> @SecretCT` and `@Secret -> @SecretCT` are rejected with
  `T030` (`CT016`).

The source rule applies at annotated bindings, returns, and direct-call
arguments. It prevents data produced outside the CT discipline from being
relabelled as if its prior computation had been constant time.

The program-counter taint stack still handles ordinary implicit flow. CT
control violations are rejected before descending into the selected body, so
the stack never uses `SecretCT` as a substitute for rejecting the timing
channel.

Function parameters, actor handler parameters, generic instantiations, and
closure captures preserve their declared or source taint. A closure body is
checked in an environment seeded from the taints of its actual captures.

## 3. Rejection inventory

Spec IDs are stable attack-surface names. User-facing diagnostics use the
T-code in the third column.

| ID | Rejected operation | Diagnostic |
|---|---|---|
| CT001 | `if` condition is `@SecretCT` | `T020` |
| CT002 | `while` condition, including a loop-carried update, is `@SecretCT` | `T021` |
| CT003 | `for` iterable or range bound is `@SecretCT` | `T022` |
| CT004 | `match` scrutinee or guard is `@SecretCT` | `T023` |
| CT005 | Array index is `@SecretCT` | `T024` |
| CT006 | `load8`/`store8` pointer, or `vec_load`/`vec_store` base or index, is `@SecretCT` | `T025` |
| CT007 | Either division operand is `@SecretCT` | `T026` |
| CT008 | Variable shift by `@SecretCT` | Reserved; no current source operator |
| CT009 | Short-circuit Boolean control by `@SecretCT` | Reserved; no current source operator |
| CT010 | Any extern-call argument is `@SecretCT` | `T027` |
| CT011 | A `DeclassifyCT` capability is consumed more than once | `O001` |
| CT012 | A closure capture carries `@SecretCT` into a forbidden operation | The applicable `T020`-`T031` code |
| CT013 | Generic monomorphization carries `@SecretCT` into a forbidden operation | The applicable `T020`-`T031` code |
| CT014 | `send`, `ask`, or `spawn` carries an `@SecretCT` payload or timeout | `T028` |
| CT015 | `alloc` or `region` size is `@SecretCT` | `T029` |
| CT016 | `@Internal` or `@Secret` is assigned, returned, or passed as `@SecretCT` | `T030` |
| CT017 | Plain `declassify` receives `@SecretCT` | `T031` |
| CT018 | Either `str` `==` / `!=` operand is `@SecretCT` | `T033` |

`declassify_ct` also requires an actual `@SecretCT` input. Other labels are
rejected with `T032`.

CT018 is a rejection, not a constant-time lowering, and the reason is worth
stating: `str` equality compares content with an early-exit byte loop, so it
leaks the common-prefix length through **two** channels — the trip count, and
the fuel consumed, which the runtime reports back to the caller. A branch-free
fold would still leak `min(len_a, len_b)` through both. There is also nothing to
build one from: `ct_eq` / `ct_select` / `ct_lt` are integer-only, and taint
results are not carried into AIR lowering, so a CT-vs-fast lowering could not be
selected on a label even if one existed. Integer `==` on `@SecretCT` remains
legal — a single instruction with no data-dependent control flow.

As with every rule here, CT018 catches operands the lattice still labels
`@SecretCT`. A value whose secrecy the lattice has already lost is not caught;
that is a property of the label propagation, not of this rule.

The committed [`../../ATTACK-MATRIX.md`](../../ATTACK-MATRIX.md) maps this
inventory to executable defenses. The generated diagnostic pages under
`docs/errors/` own user-facing remediation text.

## 4. Declassification

Declassification is explicit, capability-gated, and two-stage:

```sigil
let intermediate: i64 @Secret = declassify_ct(value, ct_cap);
let public: i64 @Public = declassify(intermediate, public_cap);
```

`declassify_ct` consumes a linear `Cap<DeclassifyCT>` and lowers
`@SecretCT -> @Secret`. Plain `declassify` consumes a separate linear
`Cap<Declassify>` and lowers `@Secret -> @Public`.

Plain `declassify` cannot skip the first stage: an `@SecretCT` argument emits
`T031`. Reusing either capability emits `O001` through the ownership pass.

The type-check implementation lives in
[`capability_tc.rs`](../../crates/sigil-compiler/src/type_check/capability_tc.rs),
and the taint transitions are enforced in
[`taint_check.rs`](../../crates/sigil-compiler/src/taint_check.rs).

## 5. CT intrinsics

SIGIL provides three typed, branch-free intrinsics:

```text
ct_eq(a: integer, b: integer) -> bool
ct_select(cond: bool, then_value: integer, else_value: integer) -> integer
ct_lt(a: integer, b: integer) -> bool
```

Their result taint is the least upper bound of their inputs. Arity and operand
types are checked like other intrinsics.

The direct Wasm emitter uses fixed instruction sequences:

- `ct_eq`: XOR followed by zero test.
- `ct_select`: mask construction and bitwise selection, without Wasm
  `select` or conditional control flow.
- `ct_lt`: subtraction and constant sign-bit extraction.

The implementation is in
[`wasm.rs`](../../crates/sigil-compiler/src/wasm.rs). The byte-level regression
test in
[`taint_ct_audit.rs`](../../crates/sigil-compiler/tests/taint_ct_audit.rs)
compiles a fixture using all three intrinsics and rejects conditional-control,
select, division, and remainder opcodes in the emitted function bodies. A
separate detector test proves that the audit notices division.

The byte audit is a regression fence for current direct emission. It is not a
proof about a downstream engine's machine-code lowering.

## 6. Enforcement ownership

| Concern | Authority |
|---|---|
| Lattice and source/sink checks | `crates/sigil-compiler/src/taint_check.rs` |
| Intrinsic typing | `crates/sigil-compiler/src/type_check/expressions/intrinsics.rs` |
| Declassification capability typing | `crates/sigil-compiler/src/type_check/capability_tc.rs` |
| Linear capability consumption | `crates/sigil-compiler/src/ownership.rs` |
| Direct Wasm sequences | `crates/sigil-compiler/src/wasm.rs` |
| Security claim boundary | `docs/SECURITY_MODEL.md` and `docs/SOUNDNESS_MATRIX.md` |
| Attack census | `ATTACK-MATRIX.md` |

Primary executable evidence:

- `taint_constant_time.rs`: rejection inventory, control flow, closure, actor,
  and source-rule coverage.
- `taint_constant_time_phase_b.rs`: declassification and CT intrinsic typing.
- `taint_ct_audit.rs`: emitted-Wasm opcode audit.
- `region_secret_compose.rs`: region and declassification composition.
- `sh-security-checkers.md` and its differential tests: declared self-host parity subset.

## 7. Explicit exclusions

The current guarantee does not cover:

- caches, predictors, speculation, page faults, shared execution units,
  scheduling, DVFS, power, EM, acoustic, or other physical channels;
- host import timing or arbitrary foreign code;
- timing introduced by Wasm engines, JITs, native compilers, or later
  optimization passes;
- trap timing, fuel exhaustion timing, or termination as an observable low
  output;
- historical runtime state such as mailbox, allocator, log, or scheduler
  effects from prior invocations;
- a transitive whole-program timing proof over helper state and environment;
- authenticity of compiler binaries or unsigned certificates.

Deployments requiring stronger side-channel resistance must pin the complete
toolchain and runtime and add platform-specific measurement and mitigation.

## 8. Maintenance contract

A language or codegen change that adds a control-flow construct, memory access,
variable-time operation, allocator, foreign boundary, actor boundary, or CT
intrinsic must classify its `@SecretCT` behavior in the same change.

The change must update, as applicable:

1. the taint checker and exact diagnostic inventory;
2. the attack matrix and generated diagnostic material;
3. negative and positive compiler fixtures;
4. the Wasm opcode audit for newly admitted CT codegen;
5. `SECURITY_MODEL.md`, `SOUNDNESS_MATRIX.md`, and residual-risk boundaries;
6. the self-host parity declaration, without widening unsupported claims.

Unsupported or ambiguous cases reject. A new construct must not inherit a
constant-time classification by omission.
