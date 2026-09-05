# SIGIL local package format and resolver contract v1

**Status:** Contract v1; explicit offline locked compiler seam implemented  
**Date:** 2026-08-04  
**Revised:** 2026-08-05  
**Applies to:** `sigil check --package` and `sigil verify-cert`

This specification defines enough package identity, source framing, dependency resolution, locking,
compatibility, and certificate binding to test the ecosystem contract without opening a public
registry or shipping a package of its own.

The compiler interface is `sigil check --package <root>`. Package mode is explicit, performs no
parent/current-directory discovery, and is always offline and locked. `sigil verify-cert --cert
<file> --package <root>` performs fresh resolution/compilation and exact package-certificate
verification. Package v1 is library-only: it selects no executable entry and cannot be run or
forged. Solver-backed refinement is an invariant of package compilation itself, not only a CLI
acceptance gate: `compile_local_package` fails closed unless that exact compilation freshly derives
`solver_verified: true`. Both CLI operations inherit this invariant.

## 1. Files and serialization

- A package root contains exactly one manifest named `sigil-package.json`.
- A workspace root may contain exactly one generated lockfile named `sigil-package.lock.json`.
- Both use UTF-8 JSON and schema `format_version: "1"`.
- Duplicate JSON keys, NaN/infinity, a byte-order mark, invalid UTF-8, and unknown fields fail.
- Tools emit keys sorted lexically, two-space indentation, LF endings, and one final newline. Readers
  do not use formatting as meaning, but lockfile byte reproducibility is a required fixture.
- There are no build scripts, manifest interpolation, environment expansion, platform shell
  commands, or network callbacks in v1.

The rules above are the normative definition of both files. Worked examples of a
conforming manifest, lockfile, and dependency layout are in the acceptance corpus (§11).

## 2. Identity and namespace

The package identity is `<namespace>/<name>`. Both components are 2–64 lowercase ASCII characters
matching `[a-z][a-z0-9_-]*`. Unicode confusables, case folding, percent encoding, alternate
separators, leading punctuation, and path components are therefore impossible in v1.

- `sigil/*` is reserved for packages admitted by this repository's release authority.
- `core/*` and names beginning `sigil-` are reserved against third-party use.
- Local experiments use a stable owner/organization namespace, not `sigil`.
- Identity comparison is byte-exact. A display name cannot affect resolution.
- Each module is the package name or starts with `<name>_`; the compiler-visible module declaration
  must equal the manifest entry.
- Manifest module `m` has exactly one v1 source path, `src/m.sigil`. Alternate source roots,
  manifest path maps, recursive source discovery, and multiple files for one module are not v1.
- All module names in one resolved graph must be globally unique, including ambient/core stdlib
  modules. A collision is an error; ordering never chooses a winner.

Namespace identity authenticates nothing. Publisher authentication is a separate release property.

## 3. Versions and compatibility

Package versions are SemVer 2.0 triples with an optional prerelease; build metadata is excluded from
v1 identities. Requirements are one of:

- exact: `=1.2.3`;
- compatible: `^1.2.3`, meaning `>=1.2.3,<2.0.0`;
- pre-1.0 compatible: `^0.2.3`, meaning `>=0.2.3,<0.3.0`; or
- patch compatible: `~1.2.3`, meaning `>=1.2.3,<1.3.0`.

Ranges, wildcards, unions, implicit operators, and prerelease selection are rejected in v1. A
prerelease is selected only by an exact requirement containing that prerelease.

A version bump is breaking when it changes source compatibility, behavior, stable errors/traps,
ring, effects, grants, host imports, taint, ownership, determinism, resource ceilings, compiler or
runtime compatibility, or module names in a way that can invalidate a conforming caller. Authority
widening, taint weakening, a lower input ceiling, or pure-to-nondeterministic behavior is breaking
even when signatures do not change. Before `1.0.0`, breaking changes increment the minor version;
after `1.0.0`, they increment the major version. Patch releases cannot widen authority or weaken a
contract.

Manifest `compiler.features` may name only `json`, `solver`, and `trace`, and every named feature
must be enabled in the current compiler build. This compatibility declaration does not weaken the
package compiler invariant: package compilation and certificate verification always require the
current compiler to have run its solver-backed refinement proofs, whether or not the manifest names
`solver`.

## 4. Legal dependency sources

The v1 resolver is offline and recognizes only:

- `workspace`: a normalized repository-relative directory beneath the declared workspace root; and
- `vendored`: a normalized relative directory beneath `vendor/` whose content hash is pinned.

Absolute paths, `..`, symlinks escaping their root, Git URLs, registry coordinates, HTTP(S), local
home-directory references, and environment-derived paths are illegal. The provisional `git` and
`registry` values are deliberately not part of schema v1. Adding either requires a new decision,
authenticated provenance, cache/yank semantics, and threat-model evidence.

If the same package identity and version appears from more than one source or with more than one
content hash, resolution fails with `E_SOURCE_CONFLICT`; source precedence is not used.

## 5. Features and optional dependencies

Features are declared names matching `[a-z][a-z0-9_-]*`. A manifest lists available features,
their feature-to-feature enables, and which optional dependency identities they activate.

- `default` is an explicit list and may be empty.
- Unknown features and feature cycles fail.
- Feature union is monotonic across all dependents; a feature cannot disable another feature.
- An optional dependency is absent unless an active feature names it.
- A feature's `optional_dependencies` entries must name dependency declarations whose
  `optional` field is `true`; a feature cannot relabel a required dependency as optional.
- `default_features: false` suppresses only the dependency's declared defaults.
- Features cannot change package identity, source, version, compiler target, module names, or a
  content hash. Feature-selected modules must still be listed in the manifest and lockfile.

The always-locked compiler has no incoming dependency edge for the root and no distinct
minimal-request field. The root lock node's `features` is therefore the complete closed active set
and is used as its own authoritative seed. The loader derives manifest defaults and feature closure
and requires:

```text
closure(lock_root_features union manifest_defaults) == lock_root_features
```

Only the root is seeded from a lock node. Every non-root feature request still comes solely from
active incoming manifest edges and default-feature policy, and its derived active set must equal
the lock. The one closed set remains bound in the graph hash and certificate. This detects added
defaults/enables omitted from a lock, but cannot recover a smaller historical request: after a
default or enable edge is removed, an old closed-set member may remain valid as an explicitly
selected root feature. Recovering that intent requires a new field and protocol revision.

## 6. Deterministic resolution

Fresh control-plane inputs are the root manifest, an explicit requested-root-feature set, and an
explicit finite inventory of workspace/vendored candidates. That requested set belongs to the
control-plane oracle/generator contract; it is not a compiler CLI flag or a distinct v1
manifest/lock provenance field. The resolver performs no discovery outside those roots and no
network I/O.

1. Validate every manifest and recompute every candidate content hash.
2. Expand active features and optional dependencies to a fixed point.
3. Intersect all requirements for each package identity.
4. Reject an empty intersection, source conflict, unavailable identity, prerelease leakage, or
   yanked candidate.
5. Select the highest non-yanked matching version from the explicit inventory.
6. Repeat expansion if selection adds feature/dependency requirements.
7. Reject dependency cycles using the final active graph.
8. Reject module collisions against the graph and the pinned stdlib module inventory.
9. Emit nodes in dependency-first topological order; lexical package identity breaks ties.
10. Emit one lockfile. A second run over the same framed inputs must be byte-identical.

The implemented compiler seam consumes an already-generated exact lock and never updates it. It
preflights non-optional structural cycles before comparing content pins: cyclic manifests cannot
carry mutually self-consistent dependency content hashes, so this makes `E_DEP_CYCLE` reachable and
attributable. All manifests and sources are still parsed, normalized, framed, and recomputed; any
acyclic hash or lock disagreement fails closed.

Only one version of a package identity may appear in a v1 graph. Conflicting requirements fail with
`E_VERSION_CONFLICT`; the resolver does not duplicate versions or rename modules.

### Stable package-layer errors

| Code | Meaning |
|---|---|
| `E_MANIFEST` | Manifest/schema/semantic validation failed |
| `E_PACKAGE_MISSING` | Required identity is absent from the finite inventory |
| `E_VERSION_CONFLICT` | No single version satisfies all requirements |
| `E_SOURCE_CONFLICT` | Identity/version has conflicting source or content |
| `E_HASH_MISMATCH` | Recomputed content or manifest hash differs |
| `E_FEATURE_UNKNOWN` | A requested/activated feature is undeclared |
| `E_FEATURE_CYCLE` | Feature enablement contains a cycle |
| `E_DEP_CYCLE` | Active package dependency graph contains a cycle |
| `E_MODULE_COLLISION` | Two inputs expose the same compiler-visible module |
| `E_YANKED` | A locked node is marked yanked, or contract-level fresh resolution has no non-yanked match |
| `E_LOCK_DRIFT` | The exact locked graph does not reproduce the manifest-derived graph |
| `E_OFFLINE_MISS` | Locked content is not available in allowed local sources |
| `E_DEP_EDGE` | A source imports a package outside its own package or direct active dependencies, or ambient stdlib imports a package module |
| `E_UNSUPPORTED_SURFACE` | Package-owned source defines an `ActorDef`, `CapTypeDef`, `ImplDef`, `TraitDef`, or `StateDef`, which package protocol v1 does not admit |
| `E_RESOURCE_LIMIT` | A package graph aggregate/depth ceiling is exceeded |
| `E_CERTIFICATE` | A well-shaped supplied package certificate differs from fresh derivation |

Errors are deterministic: a validator/resolver reports the lexically first error tuple after input
validation, not filesystem enumeration order.

The v1 package input ceilings are 1 MiB for each manifest/lock JSON file, 1 MiB for each package
source file, 256 dependency declarations per manifest, 256 locked nodes, 4,096 active dependency
edges, 256 package source modules, 16 MiB of normalized package source in aggregate, dependency
depth 128, and feature-expansion depth 64. The underlying compiler's
module/function/fuel/allocation limits continue to apply. Aggregate graph and depth violations use
`E_RESOURCE_LIMIT`; an oversized individual file fails in its relevant manifest/offline-input
class. These ceilings are contract values, not tuning hints.

## 7. Source content framing

All relative paths use `/`, are UTF-8, contain no empty, `.` or `..` component, and are sorted by
raw UTF-8 bytes. Symlinks and special files are rejected. Source text must be valid UTF-8. Before
framing, CRLF/CR become LF and trailing ASCII space/tab bytes are removed from every line, matching
the existing stdlib composition policy.

The package content digest is SHA-256 over:

```text
"SIGIL-PACKAGE-CONTENT\0V1\0"
frame(package-id)
frame(version)
frame(canonical semantic JSON of sigil-package.json with evidence hashes retained)
for each declared module in lexical order:
    frame(module-name)
    frame(relative-source-path)
    frame(normalized-source-bytes)
```

`frame(x)` is an unsigned 64-bit big-endian byte length followed by the bytes. The package manifest
may bind release evidence, but its `content_hash` is held by dependents/lockfiles, not recursively
inside itself. An exact archive/file-tree digest may also be recorded and is distinct from this
compiler-input digest.

The graph digest uses the same framing domain `SIGIL-PACKAGE-GRAPH\0V1\0` over lock nodes in emitted
order, including id, version, source kind/locator, manifest hash, content hash, the one closed active
feature set, module names, and dependency node ids. Timestamps and absolute paths never enter
either digest.

## 8. Lockfile behavior

The lockfile is generated, complete, and checked in for a package workspace. It records:

- root identity and root manifest hash;
- resolver contract id and `offline: true`;
- graph hash;
- every node's exact identity/version/source locator/manifest hash/content hash;
- the one closed active feature set, exposed modules, active dependency ids, and yank observation;
  the root set is also the idempotent locked-loader seed described in Section 5; and
- the exact stdlib composition hash and compiler compatibility requirement.

The implemented package compiler exposes no normal-selection or lockfile-update mode. Package mode
is inherently locked: `sigil check --package <root>` consumes the checked-in lockfile, performs no
selection, recomputes every input, requires every locked source locally, and fails on any graph,
feature, module, manifest, content, stdlib, or compiler drift. There is no separate `--locked`
switch because unlocked package checking is not an available operation. The compiler never repairs
a hash, rewrites the lockfile, or silently selects a substitute.

A separate, explicit control-plane tool may generate or update a lockfile from the finite local
inventory under the resolver contract in Section 6; that capability is not part of the compiler
CLI seam. The implemented seam rejects every node whose lock entry records `yanked_observed: true`
with `E_YANKED`. It exposes no `--allow-yanked` escape hatch. Any future exception for rebuilding a
yanked release would require a recorded protocol and release-policy decision plus new executable
fixtures and certificate evidence; it is not authorized by v1.

## 9. Library compilation, imports, and stdlib composition

Core stdlib modules keep their existing ambient/explicit composition path. Package resolution is
an earlier, separate stage that produces package modules in dependency-first graph order. Every
`src/<module>.sigil` is parsed and its declared module is required to equal the manifest/lock entry,
including when ambient inclusion would otherwise bypass a filename check.

The ordered package source set is passed to the compiler-of-record's `compile_library_project`
path. It runs the normal parse, type, ring, effect, taint, capability, ownership, fuel, and Wasm
passes but disables executable-entry diagnostics M003–M006. A package graph therefore needs no
`tool_main` or entry actor, and an entry-looking function in a dependency cannot select or hijack
the artifact. Package execution is not a v1 operation.

Package protocol v1 deliberately admits a narrower source surface than the full language. After
module ownership is established and before compilation is accepted, the compiler rejects every
package-owned `ActorDef`, `CapTypeDef`, `ImplDef`, `TraitDef`, and `StateDef` with
`E_UNSUPPORTED_SURFACE`. This is an ownership-specific package boundary, not a ban on the type
system: package code may continue to reference and use ambient stdlib types, and the separately
attributed compiler-coupled ambient stdlib may continue to define these item forms. Ambient code
does not thereby become package-owned or exempt a package definition with the same shape. Widening
the admitted package surface requires a protocol decision plus compiler derivation and negative
fixtures for every newly admitted authority-bearing form.

Compiler-coupled ambient stdlib inclusion remains later and separate. The compiler rejects
collisions between all package modules and every ambient module, then assigns every compiled module
to exactly one package or to the selected ambient inventory. A package source may import another
module in the same package, an active direct dependency, or selected ambient stdlib. Reverse and
transitive-only package imports fail with `E_DEP_EDGE`; ambient stdlib may not import package code.
Manifest dependency edges are therefore an upper bound on, and authority boundary for, actual
source imports—not merely resolver metadata.

## 10. Certificates and provenance

Current single-module compiler certificate schema v9 remains unchanged. The explicit package path
wraps that base certificate in strict `package-graph-v1` schema 1, adding:

- package graph hash and lockfile hash;
- ordered per-node package id/version/manifest/content hashes;
- active features and modules;
- stdlib composition hash;
- derived ring/effect/host-import/grant/taint/import facts per package plus a separately attributed
  ambient stdlib record;
- graph-level resource evidence; and
- the compiler/runtime versions that derived them.

The wrapper also binds the normalized composed-source framing hash and an explicit hash of the
compiler inputs that implement parsing, package resolution, security analysis, certificates, and
Wasm emission. The compiler identity covers the workspace manifest/lock, compiler manifest and
build script, all compiler Rust sources, the `sigil-abi` manifest/source, the exact Rust compiler,
target/profile/options, enabled compiler features, and the native Z3 identity (or the explicit
solver-off marker). Its source census therefore binds the package-level solver requirement as well
as the refinement implementation: changing or removing that requirement, changing solver
configuration, or changing native solver identity changes `compiler_identity_hash`. A solver-off
identity may be useful for non-accepting diagnostics but cannot identify a successful v1 package
compilation.

The package wrapper's base certificate has `primary_module: null`, and its module inventory is
exactly the disjoint union of package-owned modules and `ambient_stdlib.modules`. Per-package
compiler derivation is canonical:

- ring facts are `inner`, `outer`, or `trusted_outer` from parsed modules;
- effects are the exact sorted typed-function/extern effect union, including inferred effects;
- host imports are `<abi>::<extern-name>`;
- grant categories are derived from effects/imports, never granted by a manifest;
- taint contracts are sorted public function signatures such as
  `module::fn(value:Internal)->Internal`, including `Flow` where present;
- trusted surfaces are compiler-derived;
- `package_imports` records the directly imported package identities and is a subset of that
  node's active dependency ids; and
- `ambient_imports` records imported modules from the separately attributed ambient inventory.

Ambient modules carry the same derived-fact shape in `ambient_stdlib.derived`. They cannot carry
package imports. The union of package and ambient effect facts must equal the base certificate's
whole-program `effects_required`; a mismatch fails closed. Resource evidence is graph-level, not
arbitrarily attributed per package: `graph_resource_evidence_hash` binds the graph/source hashes,
compiler fuel budget, and emitted inner/outer Wasm sizes.

The compiler adjudicates only the claims it can derive from the admitted program and its typed
output. Manifest `rings`, `effects`, `host_imports`, `grant_categories`, `taint_contracts`, and
`trusted_surface` must exactly equal the facts described above; package/ambient imports and effect
conservation are likewise compiler-enforced. A `pure` determinism claim is compiler-accepted only
when the package's derived rings are exactly `["inner"]` and its effects, host imports, grant
categories, and trusted surface are all empty. As implemented, this proof does not require empty
taint contracts or empty package/ambient import lists. A contradictory compiler-adjudicated claim
fails with `E_MANIFEST`; a manifest never grants authority.

The remaining contract claims are bound assertions, not facts proved by compilation. Independent
judges, executable fixtures, and release evidence must adjudicate `stable_errors`,
`trap_conditions`, every non-`pure` determinism class (`state_relative`, `environment_relative`,
`seeded`, or `nondeterministic`), the meaning and satisfaction of `resource_contract_ref` beyond
the compiler's graph-level measurements, and the API contract/card and related evidence hashes.
Strict parsing and content hashing prove that these exact assertions were compiled; they do not
prove that the assertions are true. Package Code Start and later release acceptance therefore must
not treat a well-formed wrapper as a substitute for the relevant oracle, resource, API, or
independent-review evidence.

The accepting `compile_local_package` entry point requires the freshly derived base-certificate
witness `solver_verified: true` before it returns a successful package compilation or makes its
wrapper and Wasm available as accepted evidence. A separately named structural helper is retained
only for diagnostics and regression tests; its result is explicitly not package acceptance
evidence. Package certificate verification applies the same invariant to its fresh recompile before
exact comparison can succeed. `sigil check --package` and `sigil verify-cert --package` map a
solver-unverified package result to `R817`, write no accepted artifacts, and have no environment
override. Malformed/oversized certificate input fails at the CLI certificate gate (including
`R811` for parse/shape failure) before it can be treated as verified evidence.

The wrapper is `unsigned_local`: SHA-256 proves integrity, not publisher authentication. A later
authenticated release envelope must name the repository commit, release authority, and evidence
manifest. No public publication is authorized until that envelope and key/identity lifecycle have
a separate accepted design.

## 11. Acceptance corpus

The compiler-executable neutral package graph and its semantic obligations are under
[`../../crates/sigil-compiler/tests/fixtures/packages/neutral-boundaries/`](../../crates/sigil-compiler/tests/fixtures/packages/neutral-boundaries/).
It is test-only infrastructure and implements no published package. Acceptance fixtures
also exercise compiler-API and CLI solver fail-closed behavior and reject each package-owned v1
unsupported item form while proving that ambient stdlib types remain usable. `local_package.rs`
and `package_cli.rs` are the executable contract for everything above.
