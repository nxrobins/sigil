# Self-hosted parsing and name-resolution contract

**Status:** Implemented. This document replaces the completed SH-PARSE-MM and SH-NR-0/1/2
implementation journals with the current differential boundary.

## Parser handoff

`selfhost/parser.sigil` emits the same flat representation used by the self-hosted verification
passes. A source containing one module retains a bare `P_K_MODULE` root. A source containing two or
more modules receives a `P_K_PROGRAM` root whose children are source-ordered modules with their own
items.

The multi-module differential calls the production Rust parser and compares flattened nodes,
spans, ownership, and order. The supported corpus begins with a bare `module` declaration. Nested
modules, cross-file assembly, and `pub module` semantics are outside this projection. Attributed
non-first module boundaries remain corpus-excluded and are tracked by the parser differential.

## Name-resolution projection

`selfhost/name_resolution.sigil` consumes the flat parse tree and emits four deterministic
sections:

```text
records|pool|aliases|diagnostics
```

- `records` contains `(DefId, kind, name)` in global source preorder;
- `pool` carries resolver scratch data used by the projection;
- `aliases` contains resolved module-use aliases; and
- `diagnostics` contains name-resolution codes.

Clean programs compare records and aliases with `name_resolution::resolve`. Error programs compare
the sorted diagnostic-code multiset because the Rust resolver returns no `ResolvedProgram` after a
name error. Message and span parity are not claimed.

## Covered surface

The differential suite covers:

- deterministic DefId assignment and item-kind/name classification;
- single- and multi-module source order;
- module `use` aliases;
- N007 unresolved, malformed, or self-use errors;
- N009 cyclic module dependencies;
- N001 through N006 collision and shadowing errors;
- N011 invalid module names;
- the N011-before-N012 precedence that makes N012 unreachable under the current lowercase module
  grammar;
- injective, gap-free DefId streams on clean fixtures; and
- every `stdlib/sigil/*.sigil` unit as a clean resolution corpus.

The error corpus isolates one reachable code per fixture. This avoids claiming parity for cascade
ordering after multiple simultaneous name errors. The oracle side always calls the production
parser and resolver; it does not reimplement either algorithm in the harness.

## Invariants

1. Single-module parser output remains byte-identical when multi-module support is unused.
2. Multi-module parsing always advances or stops, and execution is bounded by Wasmtime fuel.
3. DefIds are unique and contiguous on every clean fixture.
4. Exact duplicates and invalid/case-varying module names preserve production diagnostic
   precedence.
5. Name-resolution output is deterministic across repeated executions.
6. Unsupported forms reject or remain outside the declared corpus; they are not counted as parity.

## Evidence

- `crates/sigil-runtime/tests/parser_differential.rs` owns flat-node parser parity, the
  multi-module wrapper, span containment, kind coverage, determinism, and adversarial no-trap
  checks.
- `crates/sigil-runtime/tests/name_resolution_differential.rs` owns record, alias, diagnostic,
  DefId-injectivity, stdlib, non-stub, and determinism checks.
- `selfhost/parser.sigil` and `selfhost/name_resolution.sigil` are the executable self-hosted
  implementations.
- `crates/sigil-compiler/src/parser.rs` and `name_resolution.rs` are the Rust oracle.

## Non-claims

- diagnostic message or span equality for name errors;
- cross-crate or cross-file name resolution;
- function-level or grouped imports beyond the covered grammar;
- trait orphan coherence, which belongs to trait validation;
- N008, which the production resolver does not emit; and
- whole-language parser equivalence outside the named differential corpus.

Stable SH-PARSE-MM and SH-NR slice labels remain in test names because they identify semantic
cases. Git history retains their implementation sequence; this contract owns the current truth.
