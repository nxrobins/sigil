# Public u32 byte access with network byte order

Experimental public-source `sigil/bytes` version `0.1.0-public.2`, unreviewed and not
admitted. This additive version retains the two little-endian operations and
adds the Public big-endian read needed by PNG. It does not change the historical
[complete bytes contract](../../../../contracts/bytes/API.md) or implement its
copying and confidential variants.

| Function | Signature | Result |
| --- | --- | --- |
| `bytes::read_u32_le` | `(ptr:i64@Public, len:i64@Public, offset:i64@Public) -> i64@Public` | Unsigned little-endian value in `0..=4294967295` |
| `bytes::read_u32_be` | `(ptr:i64@Public, len:i64@Public, offset:i64@Public) -> i64@Public` | Unsigned big-endian value in `0..=4294967295` |
| `bytes::write_u32_le` | `(ptr:i64@Public, len:i64@Public, offset:i64@Public, value:i64@Public) -> i64@Public` | Next offset, `offset + 4` |

All operations are inner-ring with empty effect rows, no allocation, host imports,
grants, trusted surface or ownership transfer. The caller lends a live readable
region for reads or a writable region for writes. Neither confidential arguments
nor declassification are accepted. Public pointer metadata does not prove that
the backing bytes are Public or caller-owned.

Signed lengths or offsets below zero return `-400`. Otherwise insufficient logical
space returns `-413`, using `offset <= len` followed by `4 <= len - offset` to
avoid a wrapping end calculation. Writes then reject values outside
`0..=4294967295` with `-422`. This precedence applies before any load or store.
Reads never change memory; error writes leave the entire region unchanged.
For bytes `01 02 03 04`, the big-endian read returns `16909060` and the
little-endian read returns `67305985`.

The pointer must designate a live region of the stated length in Wasm32 linear
memory. Logical bounds do not validate allocation, mapping, lifetime, ownership
or labels; violating that precondition may trap and is outside the stable-result
contract. These are borrowed-region primitives, not safe owned-buffer types.
Results are state-relative, not mathematical purity or constant-time secrecy.

The per-operation fuel ceilings are 128 for each read and 160 for writes,
including stable-error paths, measured against a matched driver control.
No loops, scratch buffers, copying, big-endian writes, labeled variants or
formal resource/admission claims are included.
