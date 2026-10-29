# Public u32 byte access

Experimental public-source `sigil/bytes` version `0.1.0-public.1`, unreviewed and not
admitted. This is only the Public read/write slice of the historical
[bytes contract](../../contracts/bytes/API.md), not its complete nine-symbol API.
`copy_into`, `bytes_internal`, and `bytes_secret` are not implemented.

| Function | Signature | Result |
| --- | --- | --- |
| `bytes::read_u32_le` | `(ptr:i64@Public, len:i64@Public, offset:i64@Public) -> i64@Public` | Unsigned value in `0..=4294967295` |
| `bytes::write_u32_le` | `(ptr:i64@Public, len:i64@Public, offset:i64@Public, value:i64@Public) -> i64@Public` | Next offset, `offset + 4` |

Both are inner-ring, with empty effect rows, no allocation, host imports, grants,
trusted surface or ownership transfer. They operate on a caller-owned borrowed
region: reads require four readable bytes, writes four writable bytes. Neither
accepts confidential parameters or declassifies them. Public pointer metadata
is not proof that the caller owns Public backing bytes; the caller must satisfy
that ownership/label precondition.

Lengths and offsets are signed i64 values. Validation returns `-400` for negative
length or offset, then `-413` if four bytes do not fit inside the logical region,
then (writes only) `-422` for a value outside `0..=4294967295`. The first applicable
error wins, before any load or store. Bounds use `offset <= len` followed by
`4 <= len - offset`, without a wrapping end calculation. Stable-error writes
leave the entire region unchanged. Successful reads perform four byte loads;
successful writes perform four stores in little-endian order.

The pointer must designate the live region of the stated length in Wasm32
linear memory. Logical bounds checks do not validate allocation, mapping, lifetime,
ownership or labels of backing memory. Violating that precondition is outside
the stable-result contract and may trap; these are not safe owned-buffer types.
Read results depend on current input bytes; writes mutate caller memory. Both are
state-relative, not mathematical purity or a constant-time secrecy claim.

The read/write fuel ceilings remain 128/160, including stable-error paths. These
are checked on the current development runtime, not authenticated by old resource
records. Copy fuel and the historical complete-package Wasm ceiling are not
claimed for this partial package. There are no loops or scratch buffers.
