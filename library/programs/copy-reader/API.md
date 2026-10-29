# Shared copy reader walkthrough

`tool::tool_main(input_ptr:i64@Public,input_len:i64@Public)->i64@Public ! {Alloc}`
copies the Public input into one fresh buffer using `bytes::copy_into`, reads
the first four bytes as an unsigned little-endian u32 with `bytes::read_u32_le`,
and returns `fmt::decimal_i64` output in the usual packed pointer/length form.
Trailing bytes are copied but do not affect the value. Fewer than four bytes
refuse; `ABCD` returns exactly `1145258561` without a newline.

The caller/runtime supplies live Public memory. There are no host imports,
grants, declassification or ownership transfers; the input buffer is unchanged.
Copy errors propagate before use. Normal input, fuel and memory limits remain
in force. The copy allocates nothing; this walkthrough requests an input-sized
destination and the formatter's normal output allocation. It deliberately
copies to exercise composition, not as a claim of an optimal reader.

This is source for the documented starter/edit/upgrade walkthrough, not an
independently materialized package or admitted release. `package-init` supplies
its actual manifest and pins, and `package-refresh` derives metadata bindings.
