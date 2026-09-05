// FE2 fixture: let/const locals, if/else, while, reassignment.
function clamp(x: number, lo: number, hi: number): number {
  let r = x;
  if (x < lo) {
    r = lo;
  } else {
    if (x > hi) {
      r = hi;
    }
  }
  return r;
}

function sum_to(n: number): number {
  let s = 0;
  let i = 0;
  while (i < n) {
    s = s + i;
    i = i + 1;
  }
  return s;
}
