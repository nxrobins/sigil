# Lexical regions and region polymorphism

**Status:** Implemented. SIGIL enforces lexical region escape discipline, supports explicit
region parameters, and reclaims module/tool bump allocations where the allocator cursor is known.

## Surface

A lexical region names a memory scope and a byte budget:

```sigil
fn fill(r: Region, dst: Vec<i64> @in r) -> i64 ! { Alloc } {
    dst.push(1);
    return dst.len();
}

fn run() -> i64 ! { Alloc } {
    region scratch(4096) {
        let values: Vec<i64> = Vec::in_region(scratch);
        let count: i64 = fill(scratch, values);
    };
    return 0;
}
```

The region-related forms are:

- `region name(limit) { ... }` for a statement-scoped lexical region;
- `Region` for a region handle parameter;
- `value: T @in r` to bind a parameter's value lifetime to region parameter `r`;
- `where region(a): region(b)` to declare that `a` outlives `b`; and
- `Vec::in_region(r)` / `Map::in_region(r)` for a collection associated with the current region
  discipline.

`region` is statement-only. Its trailing value is discarded and cannot itself become an escape
sink. Returning or storing a non-global `Region` handle is rejected like any other region escape.

## Lifetime model

Every aliasable value is assigned a `RegionId`:

```text
Global       function/heap lifetime
Param(slot)  lifetime supplied through a Region parameter
Lexical(d)   lexical region at nesting depth d
```

`Global` outlives every region. Shallower lexical regions outlive deeper ones. A parameter region
outlives lexical regions created inside its function. Distinct parameter regions are incomparable
unless a direct `where region(a): region(b)` clause relates them.

The central rule is:

```text
reject when region(value) does not outlive-or-equal region(sink)
```

`check_region_escape` in `type_check/statements.rs` owns this predicate and emits T254. A declared
outlives pair is a flat direct relation; no transitive closure is inferred.

### Provenance

Places inherit the region of their root local. An aliasable expression created inside a lexical
region and lacking a rooted provenance is conservatively assigned to that region. Scalars and
static string literals are `Global`; newly allocated strings and substring views inside a region
are region-born. Local region state is reset at each function-body entry and pruned when a lexical
region exits.

This analysis is deliberately shallow. It prevents direct lifetime escapes but does not establish
deep points-to provenance, uniqueness, or general non-aliasing. Call-site frozen/mutable alias
conflicts are handled separately by the exclusivity checker.

## Escape sinks

The same predicate governs each lifetime boundary:

| Sink | Required lifetime |
| --- | --- |
| Function return | `Global` |
| Unannotated call or extern argument | `Global` |
| `@in r` call argument | caller-side region supplied for `r` |
| Assignment | region of the destination root |
| Record field construction | region where the record is born |
| Safe collection method argument | region of the receiver |
| Unresolved call target | `Global` |

At a call, every declared `where region(a): region(b)` obligation is also checked against the
actual caller-side region handles. This prevents a callee from assuming an outlives relation that
the caller did not supply.

### Collection receiver boundary

A closed allowlist permits a region-scoped collection as the receiver of audited methods:

```text
Vec: len, capacity, get, push, set
Map: len, capacity, is_empty, get, get_or, contains, insert
```

Non-receiver arguments are still checked against the receiver's region, so a shorter-lived value
cannot be inserted into a longer-lived collection. User-defined methods and methods outside this
set use their declared `@in` contract or the normal fail-closed call boundary. The
`region_allowlist_is_closed` test pins the set.

## Runtime reclamation

Module and tool functions use Wasm global 0 as the bump-allocation cursor. `RegionBegin` snapshots
that cursor; `RegionEnd`:

1. computes `used = BUMP_PTR - saved`;
2. traps when `used > limit`; and
3. restores `BUMP_PTR` to `saved`.

Nested regions therefore reclaim in LIFO order. The limit is net allocation at region exit, not a
peak-allocation bound: an inner region may already have reclaimed before its outer region is
measured.

Reclamation and the limit check are emitted only for `ModuleFunction` and `ModuleInit`, where the
cursor identity is established. Actor handlers, actor initializers, and closures retain the static
T254 escape discipline but do not rewind memory at `RegionEnd`. This is an explicit runtime
boundary, not a whole-language reclamation claim.

`Vec::in_region` and `Map::in_region` do not create independent arenas. The handle is a static
lifetime association; allocation still uses the enclosing bump allocator. The constructed value
therefore retains its runtime-honest enclosing region rather than being promoted to an arbitrary
longer-lived handle.

## Composition

Region lifetime and information-flow checks are independent. A region-born `@SecretCT` value must
satisfy both:

- T254 prevents the allocation from outliving its region; and
- taint/constant-time diagnostics prevent unauthorized downgrade or secret-dependent operations.

A scalar may be copied out when its lifetime is independent of region memory, while its taint
label remains intact. Regions do not bypass the two-stage declassification contract.

## Diagnostics

| Code | Meaning |
| --- | --- |
| T254 | A value or region handle does not outlive its destination |
| T068 | Unsupported control flow in a scoped region body |
| T111 | Region limit is not numeric |
| T029 | Region size depends on `@SecretCT` data |
| P024 | `@in r` does not name a `Region` parameter of the same function |
| P025 | A `where region(a): region(b)` name is not a valid region parameter |

## Evidence

- `region_compile.rs`, `region_stdlib.rs`, and `region_stress.rs` cover lexical provenance and
  direct escape sinks.
- `region_poly.rs`, `region_in_parse.rs`, `region_where.rs`, and `region_type.rs` cover parameter
  regions and caller/callee obligations.
- `region_inregion.rs` covers region-associated collections and escape rejection.
- `region_secret_compose.rs` covers lifetime and taint composition.
- `crates/sigil-runtime/tests/region_runtime.rs` covers allocation, growth, reclamation, and repeated
  lexical-region execution.
- AIR and WAT snapshots pin `RegionBegin`/`RegionEnd`, limit trapping, and collection construction.

## Non-claims

- no non-lexical lifetime inference;
- no promotion or implicit deep copy across regions;
- no per-region arena or peak-allocation accounting;
- no transitive inference for `where region` clauses;
- no deep alias or uniqueness theorem; and
- no actor/closure bump-pointer reclamation.

Changes that widen any boundary must add a positive case, a shorter-lifetime rejection twin, and a
runtime or byte-level witness whenever reclamation or allocation changes.
