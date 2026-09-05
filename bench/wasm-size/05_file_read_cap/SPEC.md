# 05: file_read_cap

A capability-mediated file read. SIGIL uses an outer-ring trusted
module with FFI extern declaration; Rust uses an extern import of the
host function. Both invoke the host with the same signature.

Input: a path pointer (i64) + path length (i64)
Expected output: bytes-read (i64); host stub returns 16 (i64) for the
                 fixed 16-byte SPEC test file
Error mode: clean exit
Exit code: 0
