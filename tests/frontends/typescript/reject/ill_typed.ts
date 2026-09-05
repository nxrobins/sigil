// expect-fe: FE301
// Arithmetic on a bool is ill-typed; the translator's checker rejects it rather
// than emit SIGIL the oracle would reject with T054 (H2, the spine).
function f(a: number, b: boolean): number {
  return a + b;
}
