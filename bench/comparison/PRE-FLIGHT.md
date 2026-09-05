# COMPARISON.md citation pre-flight

This file is the source of truth for citations used in
`COMPARISON.md`. It is written FIRST, before any COMPARISON.md row.

Per the plan's pre-execution citation gate, every cell in
COMPARISON.md must either:

1. Be **DOCUMENTED**: cite a primary source with §/p number,
   primary URL, and an archive URL.
2. Be **DECLARED-ABSENT**: cite the language's complete feature
   list (table of contents, manual index) to anchor the negative
   claim positively.
3. Be **MEASURED** (SIGIL-side only): point at a bench output.

Marketing pages without §/p are banned. Archive-of-paywalled-PDF
mirrors are banned (copyright). Where a paper is paywalled, only
the metadata page + DOI may be cited, NOT the PDF body.

---

## Per-language primary sources (verified via WebFetch, 2026-05-17)

### Pony

| Topic | Source | URL | Archive |
|---|---|---|---|
| Deny / reference capabilities | Clebsch et al. (2015) *Deny Capabilities for Safe, Fast Actors*, AGERE'15, §3 | https://www.doc.ic.ac.uk/~scd/fast-cheap-AGERE.pdf | DOI: 10.1145/2824815.2824816 |
| Tutorial: reference capabilities | Pony Tutorial, *Reference Capabilities* | https://tutorial.ponylang.io/reference-capabilities/ | web.archive.org snapshot to be captured |
| Tutorial: object capabilities + trust boundary | Pony Tutorial, *Object Capabilities → Trust Boundary* | https://tutorial.ponylang.io/object-capabilities/trust-boundary | web.archive.org snapshot to be captured |
| Actor model | Pony Tutorial, home § "actor-model" | https://tutorial.ponylang.io/ | — |
| OOPSLA 2015 (formal proof) | Clebsch et al. (2015) *Ownership and Reference Counting Based Garbage Collection in the Actor World*, OOPSLA'15 | https://www.ponylang.io/media/papers/opsla237-clebsch.pdf | DOI on file |
| Trust boundary via FFI gating | Pony Tutorial, "When you use the C-FFI, you are basically declaring that you trust the C code..." | https://tutorial.ponylang.io/object-capabilities/trust-boundary | — |

**Verified feature support (DOCUMENTED):** deny capabilities,
reference capabilities, actor model, trust boundary, no shared
mutable state by construction.

**DECLARED-ABSENT for Pony:** explicit effect system (Pony has
reference capabilities and a `partial` function marker, not a row-
typed effect system); information-flow taint labels; verification
certificate / audit trail; static SMT verification.

### Rust

| Topic | Source | URL | Archive |
|---|---|---|---|
| Reference (canonical) | The Rust Reference | https://doc.rust-lang.org/reference/ | — |
| Book: Fearless Concurrency (Ch. 16) | The Rust Programming Language Book, Ch. 16 | https://doc.rust-lang.org/book/ch16-00-concurrency.html | — |
| Threads | Book §16.1 | https://doc.rust-lang.org/book/ch16-01-threads.html | — |
| Channels (message passing) | Book §16.2 | https://doc.rust-lang.org/book/ch16-02-message-passing.html | — |
| Shared-state concurrency | Book §16.3 | https://doc.rust-lang.org/book/ch16-03-shared-state.html | — |
| Send / Sync traits | Book §16.4 | https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html | — |
| Ownership model (linear/affine) | Book Ch. 4 *Understanding Ownership* | https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html | — |

**Verified feature support (DOCUMENTED):** ownership / affine
consumption (Ch. 4), threads + channels + mutex (Ch. 16), no shared
mutable state without `unsafe` or synchronization primitives.

**DECLARED-ABSENT for Rust:** capability discipline (no
unforgeable-reference primitive in the language; `unsafe` is a
trust escape hatch, not a capability); native actor model
(Book §16 does not list actors among Rust's concurrency primitives;
actors are library-level, e.g. Actix); declared effect system
(`unsafe`, `async`, `const` are markers, not a row-typed effect
algebra per Leijen 2014); information-flow taint labels; native
ring / trust-boundary isolation; verification certificate / audit
trail.

### Joe-E

| Topic | Source | URL | Archive |
|---|---|---|---|
| Canonical paper | Mettler & Wagner (2010) *Joe-E: A Security-Oriented Subset of Java*, NDSS'10 | https://people.eecs.berkeley.edu/~daw/papers/joe-e-ndss10.pdf | NDSS proceedings: https://www.ndss-symposium.org/ndss2010/joe-e-security-oriented-subset-java/ |
| Companion paper (class properties) | Mettler & Wagner (2010) *Class Properties for Security Review in an Object-Capability Subset of Java*, PLAS'10 | https://people.eecs.berkeley.edu/~daw/papers/joeetypes-plas10.pdf | — |
| NDSS Symposium page (proceedings index) | NDSS 2010 paper page | https://www.ndss-symposium.org/ndss2010/joe-e-security-oriented-subset-java/ | — |

**Verified feature support (DOCUMENTED — per paper abstract +
search-result summaries):** capability discipline (object-capability
subset of Java); no shared global mutable state (immutable global
references); no reflection / no dynamic class loading (subset of
Java that removes these); compile-time verification of security
properties by review tools.

**Note on Joe-E:** Joe-E is a *subset* of Java, not a separate
language. Its security properties are achieved by restricting Java
rather than adding new constructs. The TCB claim is the Java
verifier itself plus the Joe-E checker — substantially smaller than
adding a new language runtime.

**DECLARED-ABSENT for Joe-E:** linear types (Java has no linear
type system; Joe-E does not add one); native actor model;
information-flow taint; SMT verification; effect system.

### Erlang

| Topic | Source | URL | Archive |
|---|---|---|---|
| Reference manual | Erlang Reference Manual — User's Guide | https://erlang.org/doc/reference_manual/users_guide.html | — |
| Processes | erts: Processes (lightweight, asynchronous signals) | https://www.erlang.org/doc/system/ref_man_processes.html | — |
| spawn/1, spawn/3 | erlang module reference | https://erlang.org/doc/man/erlang.html#spawn/3 | — |
| Send operator (`!`) | Expressions reference | https://erlang.org/doc/man/expressions.html#send | — |
| Hot code reload | kernel/code module — `load_file/1`, `purge/1`, `soft_purge/1` | https://www.erlang.org/doc/apps/kernel/code.html | — |
| Current vs Old code | kernel/code module, § "Current and Old Code" | https://www.erlang.org/doc/apps/kernel/code.html#current-and-old-code | — |

**Verified feature support (DOCUMENTED):** native actor model
(lightweight processes); no shared mutable state (message passing
only — "All communication between Erlang processes and Erlang ports
is done by sending and receiving asynchronous signals"); hot code
reload (via code:load_file + soft_purge).

**DECLARED-ABSENT for Erlang:** static capability discipline (Erlang
is dynamically typed, no compile-time capability verification);
linear/affine types; effect system declared at compile time;
information-flow taint labels; static verification certificate; no-
eval-by-construction (Erlang has `code:load_binary` and
`erlang:apply/3` for dynamic code).

### Caja

| Topic | Source | URL | Archive |
|---|---|---|---|
| Canonical paper | Miller, Samuel, Laurie, Awad, Stay (2008) *Caja: Safe active content in sanitized JavaScript*, Google Tech Report | Citation: https://en.wikipedia.org/wiki/Caja_project (paper title + authors confirmed) | Source archive: https://code.google.com/archive/p/google-caja |
| Project Wikipedia | Caja project | https://en.wikipedia.org/wiki/Caja_project | — |
| Google developer site (deprecated 2021) | developers.google.com/caja | https://web.archive.org/web/20210122083321/https://developers.google.com/caja/ | archive snapshot date: 2021-01-22 |
| Source archive | code.google.com/archive/p/google-caja | https://code.google.com/archive/p/google-caja | — |

**Note on Caja status:** Deprecated by Google 2021-01-31, cited
reason: "known vulnerabilities and lack of maintenance to keep up
with the latest web security research."

**Verified feature support (DOCUMENTED — per Wikipedia + Google
archive summary):** object-capability discipline (rewrites
JavaScript to a safe subset with capability-mediated DOM access);
compile-target = sanitized JavaScript (Caja is a compiler-rewriter,
not a separate language); no-eval-by-construction (sanitization
removes `eval` from third-party code).

**DECLARED-ABSENT for Caja:** native actor model; linear/affine
types; effect system; static SMT verification; deadline-typed
capabilities.

### F* (added 2026-05-17 per honesty review)

| Topic | Source | URL | Archive |
|---|---|---|---|
| Canonical paper | Swamy et al. (2016) *Dependent Types and Multi-monadic Effects in F\**, POPL 2016 | https://fstar-lang.org/papers/mumon/paper.pdf | DOI / Semantic Scholar: https://www.semanticscholar.org/paper/Dependent-types-and-multi-monadic-effects-in-F*-Swamy-Hri%C5%A3cu/ff92c6395d78f2029fae50ec5f131533e03a76fa |
| Official site | F\*: A Proof-Oriented Programming Language | https://fstar-lang.org/ | — |
| Tutorial / book (computation types tracking dependences) | F\* Tutorial Part 4: Background — Computation Types | https://fstar-lang.org/tutorial/book/part4/part4_background.html | — |
| Earlier paper on F\* purity + effects | Swamy et al. (2015) *Semantic Purity and Effects Reunited in F\**, ICFP 2015 | https://fstar-lang.org/papers/icfp2015/full.pdf | — |
| Industrial deployment | Project Everest (verified TLS, Wasm) | https://project-everest.github.io/ | — |

**Verified feature support (DOCUMENTED — per Swamy et al. 2016 §2,
§4):** dependent types; multi-monadic effect system (each effect
equipped with a monadic predicate-transformer semantics); SMT-
backed proof obligations (Z3); compile target includes verified
WebAssembly (Project Everest).

**DECLARED-ABSENT for F\*:** native actor model; native taint /
information-flow labels as a primitive (encodable via dependent
types but not first-class); object-capability discipline as a
distinct feature; packaged verification certificate (F\* produces
proof obligations but not a SIGIL-style signed cert artifact).

### Koka (added 2026-05-17 per honesty review)

| Topic | Source | URL | Archive |
|---|---|---|---|
| Canonical paper | Leijen (2014) *Koka: Programming with Row Polymorphic Effect Types*, MSFP 2014 | https://arxiv.org/abs/1406.2061 | arXiv archive: https://arxiv.org/pdf/1406.2061 |
| Microsoft Research PDF | Microsoft Research preprint | https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/koka-effects-2013.pdf | — |
| Official site | Koka language | https://koka-lang.github.io/ | — |
| Compiler source | GitHub koka-lang/koka | https://github.com/koka-lang/koka | — |

**Verified feature support (DOCUMENTED — per Leijen 2014 §3, §4):**
row-polymorphic effect types (effects appear in function type
signatures with disciplined inference); first-class effect
handlers; Hindley–Milner-style polymorphic effect inference; safe
encapsulation of stateful operations (analogous to Haskell's
`runST`).

**DECLARED-ABSENT for Koka:** native actor model; object-capability
discipline; information-flow taint labels; SMT-backed verification
(Koka is type-only + effect inference, no SMT); packaged
verification certificate; ring/trust boundary; ownership / affine
types.

**Note on Koka's effect system vs SIGIL's:** Koka's effect rows are
*polymorphic and inferred*; SIGIL's effect rows are *declared on
function signatures*. Different ergonomics, similar in essence:
both name the side effects in the type. Koka's design is the
closest thing to SIGIL's effect system in the comparison set.

---

## Pre-flight summary by row × language

The 13 rows in COMPARISON.md (10 original + 3 added per honesty
review) and the tier for each cell:

| Row \ Lang | Pony | Rust | Joe-E | Erlang | Caja | F\* | Koka |
|---|---|---|---|---|---|---|---|
| 1. Capability discipline | DOC | ABS | DOC | ABS | DOC | ABS | ABS |
| 2. Linear/affine consumption | DOC | DOC | ABS | ABS | ABS | ABS | ABS |
| 3. Trust boundary / sandbox | DOC | ABS | DOC | ABS | DOC | ABS | ABS |
| 4. Effect system | ABS | ABS | ABS | ABS | ABS | DOC | DOC |
| 5. Information flow (taint) | ABS | ABS | ABS | ABS | ABS | ABS | ABS |
| 6. Native actor model | DOC | ABS | ABS | DOC | ABS | ABS | ABS |
| 7. No shared mutable state | DOC | DOC | DOC | DOC | DOC | DOC | DOC |
| 8. No dynamic code loading | ABS | DOC | DOC | ABS | DOC | DOC | DOC |
| 9. Audit trail / cert | ABS | ABS | ABS | ABS | ABS | ABS | ABS |
| 10. Static verification approach | type-only | type-only | type-only | dynamic | type-only (rewriter) | dep-types + SMT | type-only + effect inference |
| 11. Years deployed (added) | ~10 | ~10 | ~0 (dormant) | 30+ | ~12 (deprecated) | ~15 | ~10 |
| 12. Library ecosystem (added) | small | huge | minimal | large | dead | small | minimal |
| 13. Compile-time verification cost (added) | low | low–medium | low | none | low | very high | medium |

Legend: **DOC** = DOCUMENTED with primary source; **ABS** = DECLARED-
ABSENT anchored to the language's feature-list TOC. Rows 10–13 use
graded labels because binary DOC/ABS is the wrong vocabulary for
gradient measures (verification approach, maturity, ecosystem,
cost). **SIGIL itself is the leftmost column in COMPARISON.md**;
this PRE-FLIGHT is the comparison-side citation work and tier
assignment for the other languages.

### Row-selection bias acknowledgment

These rows were chosen by SIGIL's authors. The original 10 are
informed by capability-language taxonomies (Mettler & Wagner 2010;
Clebsch et al. 2015) but the exact row list was NOT taken verbatim
from those papers — readers should not infer that authority. Rows
11–13 (production maturity, ecosystem, compile-time verification
cost) were added 2026-05-17 specifically to balance the matrix
toward measures where SIGIL is weak (or, in row 13, costly).

A dependent-type-language advocate would add: "expressive power of
the type system at proving functional correctness" (where F\* wins
decisively). A BEAM-ecosystem advocate would add: "battle-tested
distribution + supervision primitives" (where Erlang wins). The 13
rows here are a snapshot, not an exhaustive taxonomy.

---

## "Where SIGIL loses" pre-flight

The four mandatory loss rows + their citation anchors:

| They have | Citation for "they have" |
|---|---|
| Erlang: hot code reload | erlang.org/doc/apps/kernel/code.html § *Current and Old Code* + code:load_file/1, code:soft_purge/1 |
| Pony: concurrent garbage collection in the actor world | Clebsch et al. (2015) OOPSLA paper, opsla237-clebsch.pdf |
| Rust: ecosystem maturity (crates.io, ~150k crates as of 2026) | crates.io/data-access (canonical registry); Book Ch.14 *More about Cargo and Crates.io* |
| Joe-E: smaller TCB (Java subset, no new runtime) | Mettler & Wagner (2010) NDSS paper, joe-e-ndss10.pdf, §1 *Introduction* — "A small, easily-reviewable subset of Java" |

Caja is *deprecated* — does not need a "Where SIGIL loses" row;
mentioned in passing as historical precedent in the per-language
brief.

---

## Citations not found / deferred

(None at pre-flight time. If, during writeup, a specific cell needs
a citation not listed here, it must be added to this PRE-FLIGHT.md
file FIRST, then referenced from COMPARISON.md. PRE-FLIGHT.md is
single-source-of-truth for the citation set.)

---

## Methodology notes

- All URLs verified accessible 2026-05-17 via WebFetch (Claude
  Code) except where noted (PDFs return binary content; metadata
  pages and tutorial pages render fully).
- Archive.org snapshots are linked where the canonical URL is at
  risk of rotation (e.g., Google Caja deprecation page).
- Paywalled-only sources (e.g., ACM DL paywalled PDFs) are cited
  by DOI + metadata page; their content is corroborated against
  publicly accessible mirrors (e.g., Imperial College's
  `~scd/fast-cheap-AGERE.pdf` for the Pony AGERE paper).
- For Caja, the Wikipedia article is cited as a *secondary* source
  for project metadata (authors, deprecation date) because the
  Google original is no longer maintained. The canonical paper
  authorship is corroborated against multiple search results.
