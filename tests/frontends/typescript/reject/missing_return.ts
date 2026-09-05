// expect-fe: FE306
// A non-unit function whose `if` has a non-returning else (and no trailing
// return) does not return on every path (H5; the compiler would emit T044).
function f(n: number): number {
  if (n < 0) {
    return 1;
  } else {
  }
}
