# 03: json_sum

Sum a small packed array of i64 values. SIGIL exercises the `Alloc`
effect (a buffer is allocated and populated); Rust performs the
same arithmetic without an allocator.

Input: a packed array of 5 i64 values [1, 2, 3, 4, 5] (length = 5)
Expected output: 15 (i64)
Error mode: clean exit
Exit code: 0
