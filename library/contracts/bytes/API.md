# `sigil/bytes` API contract

**Status:** Contract `0.1.0-contract.2`; no implementation  
**Package:** `sigil/bytes`  
**Modules:** `bytes`, `bytes_internal`, `bytes_secret`

## Shared preconditions and failures

Pointer/length pairs are borrowed linear-memory regions owned by the caller for the call. A pointer
must address at least `len` live bytes; violating that ownership/mapping precondition may trap in the
runtime and is not converted into a stable error. Within a valid region, functions check logical
offset/count bounds without overflowing.

Stable results:

- `-400`: a length, offset, or count is negative, or checked arithmetic is not representable;
- `-413`: requested range exceeds the declared logical region;
- `-422`: `write_u32_le` value is outside `0..=4294967295`.

Stable validation precedence is scalar validity (`-400`), then logical bounds (`-413`), then the
write value range (`-422`). A call with multiple violations returns the first applicable result in
that order. Validation completes before any store.

Successful reads return `0..=4294967295`. Successful writes/copies return the next destination
offset. No function allocates, imports a host function, requests a grant, or changes ownership.

## Public symbols

The three module rows for each operation have identical semantics and resource bounds.

| Symbol | Signature | Ownership | Ring | Effects | Grants | Taint | Determinism | Resource ceiling | Failures |
|---|---|---|---|---|---|---|---|---|---|
| `bytes::read_u32_le` | `pub fn read_u32_le(ptr: i64, len: i64, offset: i64) -> i64` | Borrowed read-only region | inner | none | none | Public inputs -> Public result | pure relative to input bytes | exactly 4 loads; ≤128 fuel | `-400`, `-413`, invalid-region trap |
| `bytes_internal::read_u32_le` | `pub fn read_u32_le(ptr: i64 @Internal, len: i64 @Internal, offset: i64 @Internal) -> i64 @Internal ! {}` | same | inner | none | none | Internal -> Internal | same | same | same, Internal result |
| `bytes_secret::read_u32_le` | `pub fn read_u32_le(ptr: i64 @Secret, len: i64 @Secret, offset: i64 @Secret) -> i64 @Secret ! {}` | same | inner | none | none | Secret -> Secret; bounds status is Secret | same | same | same, Secret result |
| `bytes::write_u32_le` | `pub fn write_u32_le(ptr: i64, len: i64, offset: i64, value: i64) -> i64` | Borrowed mutable region; writes 4 bytes on success only | inner | none | none | Public -> Public | pure relative to initial memory | exactly 4 stores; ≤160 fuel | `-400`, `-413`, `-422`, invalid-region trap |
| `bytes_internal::write_u32_le` | `pub fn write_u32_le(ptr: i64 @Internal, len: i64 @Internal, offset: i64 @Internal, value: i64 @Internal) -> i64 @Internal ! {}` | same | inner | none | none | Internal value/status; destination remains Internal | same | same | same |
| `bytes_secret::write_u32_le` | `pub fn write_u32_le(ptr: i64 @Secret, len: i64 @Secret, offset: i64 @Secret, value: i64 @Secret) -> i64 @Secret ! {}` | same | inner | none | none | Secret value/status; destination remains Secret | same | same | same |
| `bytes::copy_into` | `pub fn copy_into(dst_ptr: i64, dst_len: i64, dst_offset: i64, src_ptr: i64, src_len: i64, src_offset: i64, count: i64) -> i64` | Borrowed mutable destination/read-only source; overlap allowed | inner | none | none | Public -> Public | pure relative to initial memory | no allocation; ≤96 + 12×count fuel | `-400`, `-413`, invalid-region trap |
| `bytes_internal::copy_into` | `pub fn copy_into(dst_ptr: i64 @Internal, dst_len: i64 @Internal, dst_offset: i64 @Internal, src_ptr: i64 @Internal, src_len: i64 @Internal, src_offset: i64 @Internal, count: i64 @Internal) -> i64 @Internal ! {}` | same | inner | none | none | Internal source/destination/status | same | same | same |
| `bytes_secret::copy_into` | `pub fn copy_into(dst_ptr: i64 @Secret, dst_len: i64 @Secret, dst_offset: i64 @Secret, src_ptr: i64 @Secret, src_len: i64 @Secret, src_offset: i64 @Secret, count: i64 @Secret) -> i64 @Secret ! {}` | same | inner | none | none | Secret source/destination/status; no declassification | same | same | same |

## Operation semantics

`read_u32_le` computes `b0 | b1<<8 | b2<<16 | b3<<24` from bytes at `offset..offset+4`.

`write_u32_le` writes the low-to-high bytes of an in-range value and returns `offset + 4`. It must
perform no partial write on any stable error.

`copy_into` returns `dst_offset + count`. `count == 0` succeeds at any offset in `0..=len` without
accessing memory. When source and destination overlap, the result is as if the source range were
copied to temporary storage first. It must perform no partial write when logical validation fails.

Bounds checks use forms equivalent to `offset <= len && needed <= len - offset`; computing
`offset + needed` before validating overflow is non-conforming.

## Compatibility

Endianness, error codes/precedence, overlap behavior, partial-write guarantee, label relationships,
ownership preconditions, effects, ring, determinism, and resource formulas are public compatibility
properties. An unchecked or allocating convenience API would require a separate contract.
