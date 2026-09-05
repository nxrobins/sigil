# SIGIL security model

This document defines the boundary of SIGIL's security guarantees. The machine-checked claims
ledger in [`CLAIMS.md`](CLAIMS.md) remains the authority for what the project has executable
evidence for. The claim-by-claim evidence map is [`SOUNDNESS_MATRIX.md`](SOUNDNESS_MATRIX.md), and
accepted gaps are recorded in [`RESIDUAL_RISKS.md`](RESIDUAL_RISKS.md).

## Protected execution contract

SIGIL's production guarantees apply only when all of the following are true:

1. Source is accepted by the Rust production pipeline in `sigil-compiler`.
2. The pre-desugar typed program and resolved post-desugar AIR are projected into one canonical
   CSIR model-9 envelope containing the exact retained-v8 prefix, and the statically linked Lean
   occurrence verifier returns a zero verdict. This gate is unconditional, including solver-off
   builds.
3. Solver-dependent refinement checks run with the solver feature and complete successfully when
   the execution policy requires that tier.
4. The emitted module is executed by the matching `sigil-runtime` host.
5. A command that requires a verification certificate validates source, module, schema-v9 formal
   evidence, effects, and current solver status before execution.
6. Runtime grants are no broader than the policy supplied by the host.

The combined CSIR Lean kernel is production enforcement. The older lambda-calculus models and
self-hosted checkers remain independent evidence and do not widen the production contract.

Certificates bind source, module, and policy but are unsigned; binding does not authenticate
provenance.

## Adversary

The protected boundary assumes an attacker may control:

- SIGIL source and all source-level names, types, control flow, and values;
- source submitted through a supported foreign frontend;
- tool input bytes and actor message payloads;
- certificate files, module files, and command-line policy inputs;
- arguments supplied to host imports, including malformed pointers and lengths; and
- the order and combination in which supported language constructs are composed.

The boundary does not assume that accepted source is benign. Rejection, a deterministic trap, or a
bounded resource failure is an acceptable fail-closed result.

## Information-flow policy

SIGIL uses `Public < Internal < Secret < SecretCT`.

- Explicit value flow is tracked by least upper bound and checked at declared bindings, returns,
  direct-function and effect-operation parameters, actor message parameters, actor initialization
  parameters, state writes, and foreign boundaries.
- Effect-operation parameter labels flow into handler clause binders; perform results conservatively
  retain the least upper bound of their arguments. Because `Fn` types do not yet carry parameter
  labels, indirect calls accept only `Public` arguments rather than guessing a contract.
- Structured control dependence is tracked with program-counter taint for `if`, `while`, `for`,
  match scrutinees, and match guards. Control-dependent early exits preserve their controlling
  label on the continuation.
- Nested handler, effect-clause, closure, and region blocks use the same complete statement
  analysis as function bodies; their tail expression supplies only the enclosing expression value.
- Declassification is explicit and capability-gated. `SecretCT` requires the two-step
  `declassify_ct` then `declassify` path.
- A free non-generic function may declare parameters and its return `@Flow` — taint-POLYMORPHIC,
  quantifying over `Public`, `Internal` and `Secret`. The result's label is the least upper bound
  of the arguments, so a `@Flow` codec handed `Internal` bytes returns `Internal` bytes. This is
  not a declassification and lowers no label; it exists so a parser need not be written at a fixed
  label, refusing classified input it could safely process. Soundness comes from checking the
  annotated body once per label with every `@Flow` position instantiated to it: a body that routed
  a `@Flow` value into a `Public` sink is accepted at the `Public` instantiation and rejected at
  `Internal`, so the definition is rejected. `SecretCT` is outside the quantifier — its
  constant-time discipline constrains the code, which one body cannot satisfy both ways — and a
  `SecretCT` argument to a `@Flow` parameter is rejected (T030). `@Flow` is restricted to free
  non-generic functions because generic and impl-method bodies reach the checker through
  monomorphization, which does not carry the polymorphic label; declaring it there is an error
  rather than a silent downgrade to `Public`.
- Inside a taint-polymorphic body an unannotated `let` infers its label from its initializer
  rather than defaulting to `Public` (there is no single label such a default could mean). The
  local still carries the initializer's taint, so returns, non-`@Flow` parameters, stores and
  grants remain sinks. Everywhere else an unannotated `let` is still a `Public` declaration.
- The analysis is conservative and may reject a program whose low result is equal on all paths.

This is a static enforcement policy, not a whole-compiler noninterference theorem. In particular,
termination itself is not treated as a low output: a secret may influence whether an otherwise
accepted computation terminates. Deliberate timing, allocation, or access-pattern protection
requires `SecretCT`.

## Constant-time policy

`SecretCT` rejects source-level secret-dependent branches, loop bounds, match dispatch, memory
indices and addresses, variable-time division, foreign calls, actor crossings, and allocation
sizes. This is an algorithmic constant-time discipline over the compiler's supported operations.

It does not cover caches, speculative execution, branch predictors, page faults, power, EM, shared
hardware, operating-system scheduling, host implementation timing, or other microarchitectural and
environmental channels.

## Capability authority policy

Capability parameter types do not express a reduced per-callee authority contract. Every checked
call, spawn, message, and return sink therefore requires the full authority mask declared by the
capability type, regardless of which authorities the callee body appears to use. Restricting a
capability remains useful before direct exercise or retention, but passing a narrowed capability to
one of these sinks is conservatively rejected. This policy may reject a least-authority program; it
cannot authorize one with missing authority.

## Foreign and unsafe code

- Foreign frontends are soundness-preserving only for their documented allow-lists. Unsupported or
  ambiguous input must be rejected with an `FE` diagnostic.
- SIGIL does not verify the behavior of foreign functions. Foreign results and argument sinks are
  `Internal`; `Secret` arguments require declassification, `SecretCT` arguments are rejected with
  the dedicated constant-time diagnostic, and FFI/Unsafe effects remain explicit.
- Inline assembly, arbitrary WebAssembly, native libraries, and host code are outside the source
  language proof boundary.

## Availability and resource bounds

Fuel, parser limits, compiler limits, memory ceilings, solver resource limits, and runtime traps
bound work or fail closed. They do not guarantee availability. Exhausting a bound, terminating a
process, or refusing an input is not a confidentiality or integrity violation under this model.

## Explicit exclusions

SIGIL does not currently claim protection against:

- a malicious or compromised operating system, hardware platform, Wasmtime build, Rust toolchain,
  Z3 build, or production compiler binary;
- authenticity of an unsigned certificate or artifact;
- arbitrary handwritten WebAssembly executed outside the certificate and grant gates;
- behavior beyond a foreign frontend's declared subset;
- full semantic equivalence between the Rust compiler, self-hosted shadows, and Lean calculi; or
- correctness of Rust source-to-CSIR projection, Lean native code generation/runtime, Wasm
  emission, Wasmtime execution, or hardware timing correspondence; or
- a full source-to-runtime affine-capability/noninterference result from CSIR model 9 (Lean
  re-verifies the canonical retained-v8 envelope, derives occurrence-aware semantic least taint
  and pc-taint, and checks contracts, state/output flows, releases, T020--T033 policy classes,
  Public quantity operands, guards, and local capability shapes. The decoded raw machine has
  constructor-complete well-formedness preservation and production-linked SecretCT and Public
  delimited-release results. The Public theorem covers independently sized successful executions,
  calls, closures, recursive/private regions, per-site external inputs, repeated releases, the full
  Public projection, and ordered Public output/boundary traces; it deliberately does not equate
  ordinary-Secret timing, control, address, allocation, or cost. Complete origin/BV32/slot-meet,
  affine CFG, and quantitative balance/difference correspondence still remains load-bearing in the
  retained v6/Rust/Z3 layers, and the semantic machine is not an AIR/Wasm adequacy proof); or
- correctness of a security property merely because the corresponding model or shadow agrees.

## Fail-closed rule

Malformed, unsupported, contradictory, solver-unknown, resource-exhausted, or internally
inconsistent input must not produce a successful verified artifact. A diagnostic, trap, explicit
unsupported verdict, or process-stopping internal error is fail closed. Silent omission, defaulting
to acceptance, or treating `Unknown` as proof is not.

## Trusted computing base

| Component owner | Trusted responsibility | Included only when | Independent pressure |
|---|---|---|---|
| `sigil-compiler` | Parse, resolve, type and security checks, lowering, certificate facts, Wasm emission | Always | Self-host differential suites, Lean models, negative corpora |
| Combined Lean CSIR verifier | Fail-closed v8 decoding and resolved semantic-policy validation; direct semantic SSA/CFG taint, contracts, policy, release, guard, and local capability checks; retained v6 cyclic taint/pc, ordered capability-origin/authority/slot-meet, quantitative, and path-affine checking | Every successful source build and compilation | Kernel-checked soundness/completeness, raw-machine preservation and production-linked SecretCT relational evidence, transitive claim-dependency audit, semantic/loop/pc/capability mutants, native bridge parity, and planted-verdict mutants |
| `sigil-runtime` | Wasm isolation, import validation, grants, actor/capability tables, memory and fuel traps | Always at execution | Runtime differential census, state-machine property tests |
| `sigil-cli` and `sigil-mcp` | Certificate loading, re-derivation, policy comparison, fail-closed execution gate | Corresponding command surface | Tamper and unverified-certificate canaries |
| Wasmtime 43.0.2 | WebAssembly validation, isolation, execution semantics | Runtime execution | Lockfile pin, runtime adversarial tests |
| Z3 crate 0.12.1 / native Z3 4.12.2 | Capability and refinement query verdicts | Solver-enabled verification | Pinned native artifact, fragment guard, deterministic resource limits, corpus order tests |
| SHA-256 implementation | Source/module fingerprint binding | Certificate paths | Known-answer and same-length mutation tests |
| Rust and native dependencies | Memory safety and library semantics of the trusted host | Build and execution | Locked dependencies, CI, advisory review |
| OS and hardware | Process, filesystem, networking, clocks, and machine isolation | Deployment | Outside the in-repo proof boundary |

The pinned Lean kernel/toolchain, generated native verifier, and Lean runtime are now in the
production trusted computing base. The source-to-CSIR projector is also trusted: its exhaustive
typed-AST walks and exhaustive AIR constructor match are compiler-enforced but their semantic
correspondence is not mechanized. The projector gives mutable AIR names security-only SSA versions,
inserts predecessor-compressed phi instructions for reachable joins, and records type-proved
unreachable match fallthroughs; correctness of those strong updates and reachability facts is part
of that projection assumption. Model 9 re-verifies the retained-v8 resolved AIR envelope and its
declarative security metadata, derives semantic value/block and occurrence labels, validates
structured regions, and checks instruction-indexed destination, state, actor, FFI, and root
boundaries. Direct and dynamic calls propagate caller-pc, argument, return, capture/selector, and
callee-entry dependencies; dynamic closure targets are conservatively joined. The retained v6 obligation layer
derives a second set of cell labels and pc-taint inside Lean from seeds and monotone edges, checks cyclic graphs are
post-fixed points, and applies sink/CT/release rules to those derived labels. It also derives
capability states from a restricted origin-class vocabulary and checks BV32 restriction/split/draw
propagation, control-flow/slot authority meets, sinks, and release kinds without a projected
legitimacy bit or final authority mask. Explicit `if`/`match` and loop markers additionally drive
fallthrough-aware may-consume joins, conservative repeatable-edge checks, and `break`-exit joins in
Lean. It also checks signed quantitative cells, supported normalized literal-RHS bounds, and
mandatory guest/host split/draw guard links. It still trusts source-to-CSIR correspondence. Full
semantic capability-origin/authority/slot-meet propagation and path-affine CFG state remain legacy
obligations; quantitative split/fuel constraints remain legacy obligations rather than facts derived
solely from the v8 semantic envelope. The raw relational results are over an abstract security-event
machine and do not establish general AIR or Wasm adequacy. The raw SecretCT corollary is connected
to retained-v8 acceptance, and the independently sized Public corollary is connected to production
model-9 acceptance. Both production claim closures are fingerprinted and transitively audited.
Aggregate field precision, region aliases, closure-body rechecking under actual capture labels,
and some early-exit continuation details continue to receive mandatory enforcement from the legacy
Rust taint gate while parity work proceeds. The semantic SSA/pc-join regression corpus covers
structured branch, loop, and exhaustive-match restoration plus large sibling control-flow shapes,
but is not a source-to-CSIR correspondence proof. The other Lean calculi and self-hosted checkers
remain separate evidence sources.

## Evidence interpretation

Evidence is ordered by what it establishes, not by test count:

1. A negative canary proves a particular bad program is rejected by a named enforcement path.
2. A compositional or property test covers a class within its generator and assumptions.
3. A differential test proves agreement on its declared corpus, not correctness of either side.
4. A Lean theorem proves a stated calculus, not the Rust implementation.
5. Byte identity proves two emitters agree on an input, not that the bytes implement the source
   semantics.

Any public claim must stay within the strongest applicable statement above.
