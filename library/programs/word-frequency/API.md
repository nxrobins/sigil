# Word frequency tool contract

Experimental public-source `word-frequency/tool` version `0.1.0-public.1`, using
explicitly selected `sigil/bytes` `0.1.0-public.5` and unchanged `sigil/fmt`.
It is not an admitted library release.

`tool::tool_main(input_ptr:i64@Public,input_len:i64@Public)->i64@Public ! {Alloc}`
counts byte-exact words separated by space, tab, LF or CR. Other bytes, including
vertical tab, form feed, NUL and invalid UTF-8, belong to words. Comparisons are
case-sensitive; there is no Unicode normalization or decoding.

Output lists distinct words in first-appearance order as `word:count`, separated
by commas, with no trailing newline. Empty or separator-only input yields zero
output bytes. Commas and colons inside words are preserved without escaping;
this retains the original tool's format, not an unambiguous serialization codec.

The packed result is `pointer * 4294967296 + length`. The runtime consumes its
bytes before discarding the store. The caller supplies valid Public input memory.
The tool allocates eight bytes of metadata per word, the same output capacity
of `input_len * 3 + 32`, bounded builder record storage, and a fresh decimal
allocation per distinct word through fmt. Empty input still follows the
original zero-byte output path. There is no local endian reader/writer,
append-copy or decimal helper, formatted-pointer unpacking or output offset.
The same package's fixed-capacity `bytes_out` builder appends words, separators
and packed fmt results. Its first error is sticky and `finish` refuses instead
of publishing a prefix. Negative metadata results still refuse before use.
`bytes_scan::equal` replaces the local word-equality loop; negative comparison
results refuse instead of being treated as equal or unequal word data.

No host imports, grants or trusted code are needed. The ordinary CLI retains its
1 MiB input, 100,000 default SIGIL fuel, 10,000,000 engine fuel and 16 MiB memory
limits. Word comparisons can require quadratic work in the number of words;
inputs below the byte limit can still exhaust fuel or memory. No resource
issuance, speedup or constant-time secrecy is claimed.
