# Public byte access and bounded copying

Experimental public-source `sigil/bytes` version `0.1.0-public.3`, unreviewed and not
admitted. This version preserves the three operations from public.2 and adds
one Public borrowed-region copy. The historical complete-package contract and
its Internal/Secret variants remain separate.

| Function | Arguments, all Public i64 | Result |
| --- | --- | --- |
| `read_u32_le` | `ptr, len, offset` | Unsigned little-endian u32 |
| `read_u32_be` | `ptr, len, offset` | Unsigned big-endian u32 |
| `write_u32_le` | `ptr, len, offset, value` | Next destination offset |
| `copy_into` | `dst_ptr, dst_len, dst_offset, src_ptr, src_len, src_offset, count` | `dst_offset + count` |

All return Public i64, are inner-ring with empty effects, and use no allocation,
host imports, grants, trusted surface or ownership transfer. Reads never write.
Copy supports overlapping ranges as if the original source bytes were copied
first, without a temporary allocation. Only the destination range may change.

Negative lengths, offsets or copy count return `-400` before logical bounds
checks. Otherwise offsets beyond their declared regions or insufficient space
return `-413`. Checks use `offset <= len` then `count <= len - offset`, never an
unchecked end sum. All validation precedes the first load/store. Error copies
and writes leave memory unchanged. Writes then reject out-of-u32 values with
`-422`. Zero-count copies accept offsets through the end of both regions and
return the destination offset without accessing memory.

Pointers must designate live readable source/writable destination regions of
the declared lengths in Wasm32 linear memory, with Public backing bytes owned
by the caller for the call. Public scalar metadata alone does not establish
allocation, lifetime, mapping, ownership or backing-memory labels. Invalid
regions may trap and are outside the stable-result contract. These primitives
are not safe owned-buffer types and do not accept confidential arguments or
provide declassification.

Read fuel ceilings remain 128 and write 160. Copy's bound is 96 + 12 times
nonnegative count fuel, relative to a matched driver, including validation.
Stable-error paths must fit the 96-fuel base bound. Results are state-relative.
No new package family, host I/O, confidential variant, owned buffer, formal
resource issuance or admission is supplied.
