# Byte edit distance tool contract

Experimental public-source consumer of `sigil/bytes` and `sigil/fmt`, version
`0.1.0-public.2`; not an admitted library release.

`tool::tool_main(input_ptr: i64 @Public, input_len: i64 @Public) -> i64 @Public ! { Alloc }`
reads two byte strings separated by the first LF byte (10). Everything before
that separator is the left string; everything after it is the right string,
including further LF bytes. With no separator, the entire input is the left
string and the right string is empty. CR bytes are not stripped.

The result is decimal ASCII Levenshtein distance: each byte insertion, deletion
or substitution costs one. Adjacent transposition is not a separate operation.
UTF-8 is compared as bytes, not Unicode code points; NUL and invalid UTF-8 bytes
are ordinary data. The caller supplies a valid buffer of the stated length.

The packed result is `pointer * 4294967296 + length`; the ephemeral runtime
consumes its bytes before discarding the store. Inputs/results are Public.
The existing algorithm requests two rows of `4 * (right_length + 1)` bytes each;
`fmt::decimal_i64` requests one fresh output allocation. Bounds-checked row reads
and writes come from `sigil/bytes`; no local endian helper remains. Every negative
byte-operation result is returned as a runtime refusal, never formatted as a
distance. Explicit bytes public.5 supplies `bytes_scan::find_byte` for the
first-LF split; `-1` means no separator, while values below -1 refuse. The
valid-input Levenshtein recurrence and first-LF split are unchanged.
No host imports, grants or trusted surface are needed.

Work is quadratic in the two string lengths, plus input scanning and row setup.
The CLI caps input at 1 MiB, SIGIL fuel at a default 100,000 (explicit
1..10,000,000), engine fuel at 10,000,000 and memory at 16 MiB. These are
execution limits, not a promise that every input below the byte cap completes.
A fuel refusal is not a distance result. No formal resource issuance is implied.
