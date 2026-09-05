// FE0 fixture: a cap-free policy exercising arithmetic + an intra-program call.
function scale(x: number): number {
  return x * 3;
}

function combine(a: number, b: number): number {
  return scale(a) + scale(b) - 1;
}
