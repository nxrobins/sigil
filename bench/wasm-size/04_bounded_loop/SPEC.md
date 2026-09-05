# 04: bounded_loop

A counted loop that sums 1..=N. SIGIL emits fuel-decrement
instructions inside the loop body, visible in the Wasm code section.

Input: 1000 (i64)
Expected output: 500500 (i64 — sum of 1..=1000)
Error mode: clean exit
Exit code: 0
