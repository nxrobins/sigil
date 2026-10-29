# Public raw byte search and equality

Experimental public-source `sigil/bytes` `0.1.0-public.5`, unreviewed and not admitted.
The `bytes` and `bytes_out` modules retain public.4 byte-for-byte, including
all preceding operations, errors and resource limits. See the
[preserved API](../0.1.0-public.4/API.md).

Import `use sigil::bytes_scan;` for two Public, allocation-free readers over
arbitrary bytes. Neither function validates UTF-8 or changes input memory.

| Function | Result |
| --- | --- |
| `find_byte(ptr:i64,len:i64,offset:i64,value:i64)->i64` | Absolute index of the first matching byte at or after offset, or `-1` when absent |
| `equal(a_ptr:i64,a_len:i64,b_ptr:i64,b_len:i64)->i64` | `1` for byte-identical views, `0` for different lengths or contents |

All arguments and results are Public, both effect rows are empty, and both
functions are inner-ring with no host imports, grants, trusted surface or
declassification. Empty equal views return 1. An offset equal to length
returns -1 after scalar validation. Empty scans, empty equal views and valid
unequal-length comparisons perform no memory reads. Overlapping views are legal.

Validation precedes loads. Any negative pointer, length or offset returns
`-400`. Otherwise a scalar above 2147483647, an offset beyond length, or a view
whose pointer plus length exceeds 2147483647 returns `-413`, using subtraction
checks rather than overflow-prone sums. Search then rejects a byte outside
0..255 with `-422`, even for an empty scan. `-1` is absence, not an error.
Other negative results are errors and must never be treated as a match/boolean.

The caller supplies live readable Public memory for every view actually read.
Scalar labels and bounds do not establish backing-memory labels, ownership,
lifetime or that the region exists. Invalid backing can trap in the runtime.
These readers are not constant-time and are not confidential-label variants.

Search follows Rust memchr's first-match semantics and Python `bytes.find` on
the declared nonnegative-start, single-byte domain. Unlike Python slicing,
negative starts are errors and oversize starts refuse rather than clamp.
Equality follows Rust byte-slice/Python bytes equality on valid views. No
upstream implementation or test source is copied; this is an independently
written scalar SIGIL implementation, not a SIMD port or a whole-crate conversion.

Reference contracts: [memchr 2.8.0](https://docs.rs/memchr/2.8.0/memchr/fn.memchr.html),
[Python 3.14 bytes operations](https://docs.python.org/3.14/library/stdtypes.html#bytes.find)
and [Rust slice comparisons](https://doc.rust-lang.org/std/primitive.slice.html).
The executable regression invokes Python's real bytes operations and compares
Rust slice observations before running the SIGIL implementation. Resource
observations are local developer measurements, not formal issuance.
