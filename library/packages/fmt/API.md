# `sigil/fmt` API contract

**Status:** Public source revision `0.1.0-public.1`; implemented, experimental and not admitted
**Package:** `sigil/fmt`
**Modules:** `fmt`, `fmt_internal`, `fmt_secret`

## Shared representation and ownership

Every function returns an `i64` packed as `(ptr << 32) | len`, matching current tool conventions.
The low 32 bits are length and the high 32 bits are the pointer. The returned byte region is freshly
allocated for the invocation, does not alias caller input, and remains owned by the caller for the
runtime's invocation lifetime. There is no `free` operation in this contract.

All output is ASCII/UTF-8 with no NUL terminator. Functions are deterministic relative to their
input values and the invocation's allocation state, use no host imports or grants, and execute in
the inner ring. Fresh allocation makes each operation state-relative rather than `pure` under the
package verifier's strict empty-effect definition. Allocation exhaustion may produce the runtime's
allocation trap; there are no stable negative error values because every `i64` input is valid.

## Public symbols

| Symbol | Signature | Ownership | Ring | Effects | Grants | Taint | Determinism | Resource ceiling | Failures |
|---|---|---|---|---|---|---|---|---|---|
| `fmt::decimal_i64` | `pub fn decimal_i64(value: i64) -> i64 ! { Alloc }` | Fresh owned output | inner | `Alloc` | none | Public -> Public | state-relative | ≤20 output bytes, one allocation, ≤512 fuel | allocation trap only |
| `fmt_internal::decimal_i64` | `pub fn decimal_i64(value: i64 @Internal) -> i64 @Internal ! { Alloc }` | Fresh owned output | inner | `Alloc` | none | Internal -> Internal; no declassification | state-relative | same | allocation trap only |
| `fmt_secret::decimal_i64` | `pub fn decimal_i64(value: i64 @Secret) -> i64 @Secret ! { Alloc }` | Fresh owned output | inner | `Alloc` | none | Secret -> Secret; output bytes and packed result remain Secret | state-relative | same | allocation trap only |
| `fmt::boolean` | `pub fn boolean(value: bool) -> i64 ! { Alloc }` | Fresh owned output | inner | `Alloc` | none | Public -> Public | state-relative | ≤5 output bytes, one allocation, ≤128 fuel | allocation trap only |
| `fmt_internal::boolean` | `pub fn boolean(value: bool @Internal) -> i64 @Internal ! { Alloc }` | Fresh owned output | inner | `Alloc` | none | Internal -> Internal; no declassification | state-relative | same | allocation trap only |
| `fmt_secret::boolean` | `pub fn boolean(value: bool @Secret) -> i64 @Secret ! { Alloc }` | Fresh owned output | inner | `Alloc` | none | Secret -> Secret; output bytes and packed result remain Secret | state-relative | same | allocation trap only |

The three modules are semantically identical except for labels. A label-specific variant may not
call a weaker variant through declassification or write derived bytes into weaker memory.

## Decimal semantics

- Canonical base-10 digits, no leading zero except `0`, no plus sign, and one ASCII `-` for negative
  values.
- `-9223372036854775808` is required exactly; negating the input in signed `i64` is not a valid
  implementation strategy unless overflow is handled.
- Length is 1–20 bytes.

## Boolean semantics

- `false` -> `false`; `true` -> `true`.
- Numeric, capitalized, padded, quoted, or NUL-terminated forms are non-conforming.

## Compatibility

Changing spelling, packed representation, output ownership, label relationship, effects, ring,
state-relative determinism classification, trap behavior, or ceilings is breaking. Adding a
formatter is additive only when it does not alter existing module inclusion, authority, or artifact
ceilings.

## Deferred surface

Hex/base-N, width/padding, composite builders, and label polymorphism require separate demand and
contract evidence. Agents must not infer them from the package name.
