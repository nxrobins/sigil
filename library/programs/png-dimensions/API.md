# PNG header dimensions

`tool::tool_main(input_ptr:i64@Public,input_len:i64@Public)->i64@Public ! { Alloc }`
borrows runtime-owned Public input and returns an allocated `WIDTHxHEIGHT` byte
string packed as pointer times 4294967296 plus length, without a newline.

Input is exactly 48 ASCII hexadecimal characters representing a PNG's first
24 bytes. Both letter cases are accepted; whitespace, `0x`, odd lengths and
extra data are refused. The decoded header must have the eight-byte PNG
signature, a first chunk length of 13, the literal IHDR chunk type, and width
and height each in 1..2147483647. PNG's big-endian fields use checked
`bytes::read_u32_be` from the explicitly selected bytes `0.1.0-public.4`. Both decimal
strings come from `fmt::decimal_i64`; the application has no duplicate reader
or integer renderer. The same package's `bytes_out` builder joins the formatted
results and separator in a fixed 21-byte backing region, enough for two
ten-digit dimensions. There is no application-side unpacking, offset tracking
or output-copy loop. The first builder error makes `finish` refuse.

Malformed hex/length returns -400, wrong signature/chunk framing -401 and
invalid dimensions -422. Negative dependency results propagate before use.
These negative entry results are refusal sentinels, not successful output or
new registered diagnostics: the existing tool runtime reports a trapped result
and the CLI returns its existing execution-refusal diagnostic.

The tool does not read files, verify CRCs, inspect the remaining IHDR fields,
decode pixels or certify that a complete PNG exists. A fabricated prefix with
valid dimensions is sufficient. Use it for metadata inspection, not image
validation. It has no host imports, grants, trusted surface, declassification
or ownership transfer. Caller ownership/backing-memory labels remain runtime
preconditions; execution fuel and memory caps still apply. Successful requests
allocate a 24-byte decoded header, two decimal strings, a fixed output backing
and bounded builder record storage. The builder does not grow its capacity.

The prefix rules follow the W3C PNG specification's
[signature and chunk layout](https://www.w3.org/TR/PNG-Structure.html),
[IHDR dimensions](https://www.w3.org/TR/PNG-Chunks.html#C.IHDR), and
[integer byte order](https://www.w3.org/TR/PNG-DataRep.html#DR.Integers-and-byte-order).
This experimental experimental tool is unreviewed and not admitted.
