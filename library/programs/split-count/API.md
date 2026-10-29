# Split-count tool contract

Experimental public-source consumer of `sigil/fmt`; not an admitted library release.

`tool::tool_main(input_ptr: i64 @Public, input_len: i64 @Public) -> i64 @Public ! { Alloc }`
reads the supplied byte buffer and returns the decimal ASCII field count. Empty
input has zero fields; every nonempty input has one plus its number of comma
bytes (44). This is a byte-level delimiter counter, not a quoted CSV parser.
Adjacent, leading and trailing commas all count. UTF-8 and embedded NUL bytes
have no special meaning. The caller supplies a valid buffer of the stated length.

The result encodes `pointer * 4294967296 + length`. Its bytes belong to the
ephemeral runtime instance, which consumes them before discarding the store.
Formatting uses `fmt::decimal_i64`, with its exact-size output allocation and
Public label contract. No host imports, filesystem/network grants or trusted
surface are needed. Labels are preserved; this profile is not a confidential
data entry point.

Resource bounds for the documented CLI path: input at most 1 MiB, default SIGIL
fuel 100,000 (explicit 1..10,000,000), engine fuel 10,000,000, linear memory
16 MiB. Long inputs can exhaust fuel; a bounded failure is not an incorrect
count. The package declaration describes intent, not independent admission.
