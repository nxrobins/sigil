// expect-fe: FE301
// A call whose argument count disagrees with the declaration is rejected by the
// translator's type checker (rather than producing SIGIL the oracle rejects).
function g(a: number, b: number): number {
  return a + b;
}

function f(a: number): number {
  return g(a);
}
