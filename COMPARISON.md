# SIGIL vs Pony / Rust / Joe-E / Erlang / Caja / F\* / Koka — feature comparison

> **Scope of claim:** This is a **feature comparison** with primary-
> source citations. It is **not a runtime performance benchmark** —
> we did not build equivalent programs in Pony, Joe-E, Erlang, Caja,
> F\*, or Koka and measure them. The Wasm-size comparison in
> [`PERFORMANCE.md`](PERFORMANCE.md) is SIGIL-vs-Rust only. **n = 5
> paired programs** for the size comparison is a credibility
> instrument, not a complete characterization. Workloads are author-
> chosen and skew toward small, capability-mediated programs; we
> explicitly do not benchmark crypto, heavy numeric, or GC-heavy
> code.
>
> **Row-selection bias disclosure (added 2026-05-17).** The 13 rows
> below were chosen by SIGIL's authors. The first 10 are *informed
> by* — not lifted verbatim from — capability-language taxonomies
> (Mettler & Wagner 2010; Clebsch et al. 2015). Rows 11–13 were
> added specifically to balance the matrix toward measures where
> SIGIL is weak (production maturity, ecosystem) or costly
> (compile-time verification cost). Even with these additions, the
> row list is still authored by us and unavoidably reflects our
> sense of what matters. Treat this matrix as **"where SIGIL sits
> in the design space"**, not **"who has the most features."** A
> dependent-type-language advocate would add rows on type-system
> expressive power; a BEAM-ecosystem advocate would add rows on
> distributed-systems primitives; both would change the picture.

Every cell in the matrix below is tagged with one of three scope-of-
claim tiers (mirroring the [CVE corpus's](CVE-MATRIX.md) honesty
mechanism):

| Tier | Meaning |
|---|---|
| **DOC** (DOCUMENTED) | Primary source cited with §/p reference. The cell content is supported by an official language reference, RFC, or canonical paper. |
| **ABS** (DECLARED-ABSENT) | The language lacks this feature. Anchored to the language's complete feature list (table of contents, manual index) so the negative claim is positively backed. |
| **MEASURED** | SIGIL-side only. Number from PERFORMANCE.md. |

The citation source of truth is
[`bench/comparison/PRE-FLIGHT.md`](bench/comparison/PRE-FLIGHT.md),
written first per the v2 plan's pre-execution citation gate. Every
URL was verified accessible 2026-05-17 via WebFetch; paywalled
sources are cited by DOI + metadata page (no copyright-violating
PDF mirrors).

---

## Per-language briefs

### SIGIL

Capability-secure actor language targeting WebAssembly. Inner-ring
(default) modules cannot declare FFI or Unsafe effects; outer-ring
trusted modules can, but their callers must obtain explicit
capabilities. Static verification by row-typed effects + Z3
capability-attenuation proofs + ownership / linearity checks. Two-
module Wasm output preserves ring isolation at the import-section
level. Compile target: **WebAssembly**.

### Pony [1]

Concurrent actor language with **deny capabilities** (reference
capabilities). Type system rejects data races at compile time. Uses
concurrent garbage collection in the actor world (proved correct,
Clebsch et al. OOPSLA 2015). No effect system in the row-typed sense;
no static information-flow tracking. Compile target: native via LLVM.

### Rust [2]

Systems language with **ownership / affine types** (Book Ch. 4) and
explicit concurrency primitives — threads + channels + mutex
(Book Ch. 16). `unsafe` is a syntactic trust escape hatch, not a
capability. No native actor model in the standard library; actors
are library-level (e.g. Actix). Compile target: native (LLVM) and
WebAssembly.

### Joe-E [3]

Object-capability **subset of Java** (NDSS 2010). Achieves security
properties by *removing* Java features (reflection, dynamic class
loading, global mutable state) rather than adding new constructs.
The TCB is the Java verifier plus the Joe-E checker — substantially
smaller than adding a new language runtime. Compile target: JVM
(executes as Java bytecode).

### Erlang [4]

Dynamically-typed actor language for telecom-scale systems. **Native
lightweight processes** (millions per node) with asynchronous
message passing; no shared mutable state by construction. **Hot code
reload** via `code:load_file/1` + `code:soft_purge/1` is a defining
operational feature. No static type system in the classical sense;
no compile-time capability discipline. Compile target: BEAM VM.

### Caja [5]

Object-capability **JavaScript sanitizer** (Google, 2008–2021).
Rewrites untrusted third-party JavaScript into a safe subset; uses
wrapper objects to mediate DOM access. **Deprecated by Google in
January 2021** citing "known vulnerabilities and lack of maintenance
to keep up with the latest web security research." Compile target:
sanitized JavaScript.

### F\* [6]

Dependent-type proof-oriented language (Microsoft Research, 2011–
present). **Multi-monadic effect system** (each effect equipped with
a monadic predicate-transformer semantics; Swamy et al. POPL 2016)
and **SMT-backed proof obligations** (Z3). Programs prove
functional correctness, not just type safety. Industrial deployment:
Project Everest (verified TLS implementation; verified WebAssembly
output). Compile target: OCaml, F#, C, WebAssembly.

### Koka [7]

Research language for **row-polymorphic effect types** (Microsoft
Research / Daan Leijen, 2014–present). Effects appear in function
type signatures via row polymorphism with duplicate labels; effect
inference is Hindley–Milner-style. **First-class effect handlers**
let users implement custom control structures (exceptions, async/
await, generators) as library code. Compile target: C, JavaScript,
WebAssembly.

---

## Feature matrix

13 rows. The first 10 are informed by capability-language
taxonomies (see row-selection bias disclosure above). Rows 11–13
were added 2026-05-17 to surface measures where SIGIL is weak or
costly — see "Where SIGIL loses" below. Compile target is NOT a
row (orthogonal architectural choices are not comparable features;
see per-language briefs above instead).

| # | Feature | SIGIL | Pony [1] | Rust [2] | Joe-E [3] | Erlang [4] | Caja [5] | F\* [6] | Koka [7] |
|---|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| 1 | Capability discipline (unforgeable refs) | DOC | DOC | ABS | DOC | ABS | DOC | ABS | ABS |
| 2 | Linear / affine consumption | DOC | DOC | DOC | ABS | ABS | ABS | ABS | ABS |
| 3 | Trust boundary / sandbox | DOC (ring system) | DOC (ponyc --safe) | ABS | DOC (subset-of-Java) | ABS | DOC (sanitization rewriter) | ABS | ABS |
| 4 | Effect system (declared side effects) | DOC (row-typed) | ABS | ABS | ABS | ABS | ABS | DOC (multi-monadic) | DOC (row-polymorphic) |
| 5 | Information flow / taint labels | DOC | ABS | ABS | ABS | ABS | ABS | ABS (encodable via DT) | ABS |
| 6 | Native actor model | DOC | DOC | ABS | ABS | DOC | ABS | ABS | ABS |
| 7 | No shared mutable state by construction | DOC | DOC | DOC (without `unsafe`) | DOC | DOC | DOC | DOC | DOC |
| 8 | No dynamic code loading (no `eval`) | DOC | ABS | DOC | DOC | ABS | DOC | DOC | DOC |
| 9 | Audit trail / verification certificate | DOC | ABS | ABS | ABS | ABS | ABS | ABS (proof obligations only) | ABS |
| 10 | Static verification approach | type-only + SMT (Z3) | type-only | type-only | type-only | dynamic | type-only (rewriter) | dep-types + SMT (Z3) | type-only + effect inference |
| 11 | Years deployed / maturity | research-stage (~0) | ~10 | ~10 stable | ~0 (dormant) | 30+ | ~12 (deprecated 2021) | ~15 (active) | ~10 (active research) |
| 12 | Third-party library ecosystem | none | small (Corral) | huge (~150k+ crates.io) | minimal | large (BEAM + Elixir) | dead | small (Project Everest libs) | minimal |
| 13 | Compile-time verification cost | high (Z3 dominates) | low | low–medium | low | none (runtime) | low | very high (SMT proofs) | medium (effect inference) |

Cells marked DOC are supported by primary-source citations in
[`bench/comparison/PRE-FLIGHT.md`](bench/comparison/PRE-FLIGHT.md).
Cells marked ABS anchor the negative claim to the language's full
feature list (table of contents, manual index, paper §); the
anchor is recorded per cell in PRE-FLIGHT.md. Rows 10–13 use
graded labels because binary DOC/ABS is the wrong vocabulary for
gradient measures.

Cells with extra text (e.g., "ring system", "ponyc --safe", "multi-
monadic") use the language's own terminology for the closest analog.
These are NOT claims of equivalence — they're naming conventions.

---

## Where SIGIL loses

Each row uses the triadic structure (They have / Why it matters /
What SIGIL trades). Expanded 2026-05-17 to **6 rows** (was 4) to
match the matrix's enlarged comparison set and to surface losses
proportionate to the wins listed below. Caja is omitted (deprecated;
comparing against a dead project would be misleading).

### Erlang — hot code reload [4]

**They have:** `code:load_file/1` + `code:soft_purge/1` semantics
that swap a running module's code while preserving in-flight
processes. The BEAM VM maintains "current" and "old" code variants
simultaneously per module ([erlang.org/doc/apps/kernel/code.html
§ Current and Old Code](https://www.erlang.org/doc/apps/kernel/code.html)).

**Why it matters:** Telecom-scale systems patch live without
downtime. The 9-nines availability stories told about Erlang are
built on this primitive. Operational maturity SIGIL cannot match.

**What SIGIL trades:** SIGIL's verification certificate ties a
specific compiled Wasm module to a specific source SHA-256 and a
specific effect/capability allowance set. Hot-swapping the running
module would invalidate the certificate. SIGIL prioritizes a **static
audit trail** over **operational fluidity**. We accept the trade.

### Pony — concurrent garbage collection in the actor world [1]

**They have:** A GC algorithm proved correct for concurrent actors
(Clebsch et al. OOPSLA 2015, *Ownership and Reference Counting Based
Garbage Collection in the Actor World*). Production-grade GC tuned
over years; deny capabilities enforce data-race freedom at compile
time even with this GC running.

**Why it matters:** Actor systems with shared heap need to reclaim
memory; without good GC the programmer must hand-manage lifetimes.
Pony delivers both safety + ergonomics + low pause times.

**What SIGIL trades:** SIGIL has no concurrent GC; allocation lives
in linear regions or capability-mediated heaps. SIGIL programs that
would benefit from a shared GC must instead use the linear-cap and
region disciplines. Less ergonomic for some workloads (object
graphs); more transparent about lifetime.

### Rust — ecosystem maturity [2]

**They have:** ~150,000+ crates on crates.io, mature Cargo
toolchain, established editor integrations, ~10 years of production
deployment. Documentation is comprehensive; community is large.

**Why it matters:** Real software builds on libraries. A language
with no crypto / serialization / HTTP libraries is academic. Rust's
ecosystem makes day-2 productivity attainable.

**What SIGIL trades:** SIGIL is research-stage. There are no third-
party libraries. The compiler is one PR away from being correct in a
new corner case. This is a "v0" credibility instrument, not a
production language. We trade ecosystem for being able to make
correctness claims that are verifiable end-to-end.

### Joe-E — smaller TCB claim [3]

**They have:** Joe-E is a *subset* of Java, not a new language.
The TCB is the existing Java verifier plus the Joe-E checker — a
much smaller addition than introducing a new compiler and runtime.
Mettler & Wagner (2010) §1: "A small, easily-reviewable subset of
Java."

**Why it matters:** Smaller TCB → fewer bugs of-its-own → less to
audit. A pre-existing platform (the JVM) bears most of the runtime
correctness burden; Joe-E only adds a checker.

**What SIGIL trades:** SIGIL ships a new compiler, a new runtime,
and a new ABI. Each adds attack surface relative to running on the
JVM. We trade JVM piggy-backing for: a smaller language to formally
reason about, dedicated capability primitives, and a WebAssembly
target with sandboxed deployment.

### F\* — dependent types prove functional correctness [6]

**They have:** Dependent types + SMT-discharged proof obligations
let F\* prove arbitrary functional correctness properties: that a
sort function sorts, that a parser is sound, that a TLS handshake
implementation matches its protocol spec (Project Everest /
miTLS). F\*'s effect system is multi-monadic — strictly more
expressive than SIGIL's row-typed effects in the sense that you can
encode SIGIL's effect rows as F\* monads but not vice versa.

**Why it matters:** F\* can verify properties SIGIL can't even type-
check. SIGIL guarantees capability-discipline and absence of
forbidden effects; F\* guarantees that a specific algorithm
implements a specific mathematical relation. Different rung on the
verification ladder.

**What SIGIL trades:** F\*'s verification cost is very high (proof
obligations, manual lemma writing, SMT solver tuning) and the
language is heavyweight. SIGIL deliberately stops at "capability +
effect + taint discipline" — the easier-to-deploy 80% of formal
guarantees, with a much lighter cognitive footprint for the
developer.

### Koka — first-class effect handlers, more ergonomic effect inference [7]

**They have:** Row-polymorphic effect types with Hindley–Milner
*inference* (no need to declare effects on every signature; Koka
infers them) and **first-class effect handlers**. Handlers let
users implement async/await, generators, custom exception types as
library code — no compiler intervention needed.

**Why it matters:** Effects-as-library-features is a more flexible
design point than effects-as-built-in-keywords. Koka's effect rows
compose more cleanly than SIGIL's per-function declared rows; a
program that needs a new control structure can implement it without
language changes.

**What SIGIL trades:** SIGIL's effects (`FFI`, `Unsafe`, `Alloc`,
custom) are *declared on signatures*, not inferred — explicit but
verbose. SIGIL has no handler mechanism; effects are static
capabilities the compiler must allow at each call site. We trade
ergonomics for: each effect-row in the source is auditable by
inspection without running an inference step.

### Production maturity — every comparison language except Joe-E has more

**They have:** Pony has ~10 years of stable releases. Rust has been
stable since 2015 (~10 years), with industrial deployment from
Mozilla, AWS, Microsoft, the Linux kernel. Erlang has 30+ years of
telecom-scale production. F\* has ~15 years and Project Everest /
miTLS in production. Koka has ~10 years of active development.

**Why it matters:** Real software needs language-level bugs fixed,
ecosystem libraries to glue together, compilers that work on the
target hardware, and a community to ask questions of. "Years
deployed" is the dominant predictor of "this language won't waste
my time."

**What SIGIL trades:** SIGIL is research-stage. There are no third-
party libraries; the compiler is one PR away from being correct in
a new corner case; the language has shipped no production code.
We trade industrial-readiness for the freedom to make foundational
changes (cap-types, ring system, effect rows) without breaking a
deployed user base.

---

## What SIGIL has that others don't

Symmetric to the losses above. **Revised 2026-05-17** to honestly
acknowledge that the original "effect rows" claim is no longer
exclusive after F\* and Koka were added to the comparison.

- **The combination** of: capability discipline + linear/affine caps
  + native actor model + row-typed effects + information-flow taint
  + Z3-backed capability proofs + verification certificate. No
  language in the comparison set assembles all of these in one
  design. The individual pieces exist elsewhere — Pony has caps and
  actors; F\* has SMT-backed verification; Koka has effect rows;
  Erlang has the actor model — but the combination is SIGIL-
  specific.
- **Z3-backed capability attenuation proofs.** SIGIL uses SMT to
  verify the capability *lattice* (e.g., that a restricted
  capability cannot be passed to a sink that requires full
  authority). F\* uses Z3 for functional-correctness proof
  obligations, not for capability-lattice verification specifically;
  the two solver invocations have different shapes.
- **Information-flow taint labels** (`@Public`, `@Internal`,
  `@Secret`) with compile-time `can_flow_to` checks as a first-
  class language feature. F\* can *encode* information-flow via
  dependent types but it's not primitive; the other six comparison
  languages have no equivalent.
- **Verification certificate** binding source SHA-256 → compiled
  Wasm SHA-256 → declared effect set. The `sigil verify-cert`
  command makes this auditable post-build. F\* produces proof
  obligations (which can be audited) but not a packaged signed
  cert artifact in the SIGIL sense. The other six have nothing
  analogous.
- **Two-module ring-isolated Wasm output.** Inner-ring and outer-
  ring modules share no imports; capability boundaries are visible
  at the Wasm import-section level. Unique to SIGIL across the
  comparison set.

What was claimed in the v1 of this doc and IS NOT exclusive to
SIGIL: row-typed effect systems (Koka has them; F\* has multi-
monadic equivalents). SIGIL's effect rows are declared rather than
inferred, which is a different design point than Koka — but neither
is "unique." We removed that claim from this section.

---

## Citations

All citations are recorded with §/p references in
[`bench/comparison/PRE-FLIGHT.md`](bench/comparison/PRE-FLIGHT.md).
Summary:

[1] Clebsch, S., Drossopoulou, S., Blessing, S., McNeil, A. (2015).
*Deny Capabilities for Safe, Fast Actors.* In Proceedings of the
5th International Workshop on Programming Based on Actors, Agents,
and Decentralized Control (AGERE '15), §3. DOI:
[10.1145/2824815.2824816](https://dl.acm.org/doi/10.1145/2824815.2824816).
Open access mirror: [doc.ic.ac.uk/~scd/fast-cheap-AGERE.pdf](https://www.doc.ic.ac.uk/~scd/fast-cheap-AGERE.pdf).
Pony tutorial reference: [tutorial.ponylang.io/reference-capabilities/](https://tutorial.ponylang.io/reference-capabilities/).

[2] *The Rust Programming Language* (Klabnik & Nichols). Specifically
Ch. 4 *Understanding Ownership* and Ch. 16 *Fearless Concurrency*.
[doc.rust-lang.org/book/](https://doc.rust-lang.org/book/). For
language semantics: [doc.rust-lang.org/reference/](https://doc.rust-lang.org/reference/).

[3] Mettler, A., Wagner, D., Close, T. (2010). *Joe-E: A Security-
Oriented Subset of Java.* In Proceedings of the Network and
Distributed System Security Symposium (NDSS 2010). NDSS proceedings
page: [ndss-symposium.org/ndss2010/joe-e-security-oriented-subset-java/](https://www.ndss-symposium.org/ndss2010/joe-e-security-oriented-subset-java/).
Direct PDF: [people.eecs.berkeley.edu/~daw/papers/joe-e-ndss10.pdf](https://people.eecs.berkeley.edu/~daw/papers/joe-e-ndss10.pdf).
Companion: Mettler & Wagner (2010), *Class Properties for Security
Review in an Object-Capability Subset of Java*, PLAS 2010.

[4] *Erlang/OTP Documentation.* Specifically: [erlang.org/doc/system/ref_man_processes.html](https://www.erlang.org/doc/system/ref_man_processes.html)
(processes + message passing), [erlang.org/doc/apps/kernel/code.html](https://www.erlang.org/doc/apps/kernel/code.html)
(hot code reload; § *Current and Old Code*), [erlang.org/doc/man/erlang.html#spawn/3](https://erlang.org/doc/man/erlang.html#spawn/3)
(spawn function reference).

[5] Miller, M.S., Samuel, M., Laurie, B., Awad, I., Stay, M. (2008).
*Caja: Safe active content in sanitized JavaScript.* Google Tech
Report. Project Wikipedia: [en.wikipedia.org/wiki/Caja_project](https://en.wikipedia.org/wiki/Caja_project)
(authoritative for project metadata; the Google original was
deprecated 2021-01-31). Source archive: [code.google.com/archive/p/google-caja](https://code.google.com/archive/p/google-caja).

[6] Swamy, N., Hriţcu, C., Keller, C., Rastogi, A., Delignat-Lavaud,
A., Forest, S., Bhargavan, K., Fournet, C., Strub, P.-Y., Kohlweiss,
M., Zinzindohoue, J.-K., Zanella-Béguelin, S. (2016). *Dependent
Types and Multi-monadic Effects in F\**. POPL 2016. Paper PDF:
[fstar-lang.org/papers/mumon/paper.pdf](https://fstar-lang.org/papers/mumon/paper.pdf).
Project site: [fstar-lang.org](https://fstar-lang.org/). Industrial
deployment: [project-everest.github.io](https://project-everest.github.io/).

[7] Leijen, D. (2014). *Koka: Programming with Row Polymorphic
Effect Types.* Mathematically Structured Functional Programming
(MSFP) 2014. arXiv: [1406.2061](https://arxiv.org/abs/1406.2061).
Microsoft Research PDF: [koka-effects-2013.pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/koka-effects-2013.pdf).
Project site: [koka-lang.github.io](https://koka-lang.github.io/).

---

## Cross-references

- [`PERFORMANCE.md`](PERFORMANCE.md) — measured throughput +
  Wasm-size numbers.
- [`bench/comparison/PRE-FLIGHT.md`](bench/comparison/PRE-FLIGHT.md)
  — citation source of truth.
- [`ATTACK-MATRIX.md`](ATTACK-MATRIX.md) and
  [`CVE-MATRIX.md`](CVE-MATRIX.md) — SIGIL's security story.
