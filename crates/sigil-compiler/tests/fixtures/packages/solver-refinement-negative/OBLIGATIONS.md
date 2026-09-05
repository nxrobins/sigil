# Solver refinement negative fixture

This test-only package is not a library candidate. Its literal `Index { value: 42 }` contradicts
the compiler-checked refinement `value > 100`.

- A solver-enabled package check must reject it with `T210`.
- A solver-off package check may complete structural compilation internally, but the CLI must fail
  with `R817` before emitting Wasm, a package certificate, JSON certificate data, or an OK verdict.
- Changing `42` to `101` is the deliberate accept-side mutation.
