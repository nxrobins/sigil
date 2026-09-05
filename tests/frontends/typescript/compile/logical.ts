// FE2 fixture: && / || desugared to a bool temp + guarded if (short-circuit
// preserved: the RHS is evaluated only on the reachable path).
function both(a: number, b: number): boolean {
  return a < b && b < 10;
}

function either(a: number, b: number): boolean {
  return a == 0 || b == 0;
}
