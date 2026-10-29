# Public bytes and bounded output builder

Experimental public-source `sigil/bytes` version `0.1.0-public.4`, unreviewed and not
admitted. Module `bytes` retains public.3 byte-for-byte; its four Public u32
and copy operations, errors and resource limits are unchanged. See the
[preserved bytes API](../0.1.0-public.3/API.md).

Import `use sigil::bytes_out;` from the same package for a fixed-capacity builder.
All parameters, fields and results are Public. `Builder` is an existing SIGIL
record, not a new compiler type, capability, owned-buffer proof or opaque handle.

| Function | Result and effect |
| --- | --- |
| `new(capacity:i64)` | `Builder`; Alloc for fixed output backing, plus bounded record storage |
| `append(out:Builder @Mut,src_ptr:i64,src_len:i64,src_offset:i64,count:i64)` | New length or negative error; delegates to overlap-safe `bytes::copy_into` |
| `append_output(out:Builder @Mut,packed:i64)` | Appends a packed Public output such as fmt's result, without caller-side pointer/length unpacking |
| `push_byte(out:Builder @Mut,value:i64)` | New length or negative error; appends one byte in 0..255 |
| `finish(out:Builder @Mut)` | Packed output `pointer * 4294967296 + length`, or the first negative error |

Construction accepts capacity 0..2147483647. Negative capacity records `-400`;
larger capacity records `-413`, without allocating output backing. Construction
still creates bounded record storage. Native memory/fuel caps may refuse an
otherwise valid request; capacity is not a promise that allocation will succeed.

Append inherits copy's scalar-before-bounds validation and `-400`/`-413` errors.
Push checks the destination slot before the byte range: full output gives
`-413`; otherwise an invalid byte gives `-422`. Negative packed output is
preserved as an error without decoding or memory access. Empty appends perform
no source access. No operation grows the backing allocation.

The first operation failure is sticky. That operation leaves output bytes and
length unchanged, records the error, and later append/push calls return it
without writing. `finish` refuses instead of publishing the already-built
prefix. Previously successful writes are retained, not transactionally rolled
back. There is no reset or automatic recovery API.

Use constructor-produced records only through these functions; do not forge or
mutate fields. The record is not construction-sealed. Source regions must be
live, readable, caller-owned Public memory. Scalar labels do not prove backing
labels, lifetime or ownership. Aliasing output bytes is supported by the copy
operation; source/destination must not alias the builder record itself. Records
remain within the store lifetime; successful finish borrows its output bytes.

Only construction allocates dynamic output backing. Append, packed append,
push and finish have empty effect rows; resource observations include bounded
record handling and are tested separately from the unchanged copy limits.
All functions are inner-ring, without host imports, grants, trusted surface,
declassification or confidential variants. This is local developer evidence,
not formal admission or new resource issuance.
