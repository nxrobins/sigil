// expect-fe: FE301
// `&&`/`||` in a `while` condition are non-hoistable (the condition re-evaluates
// each iteration) → rejected (M8 anti-goal; lift the test into a helper).
function f(n: number): number {
  let i = 0;
  while (i < n && i < 5) {
    i = i + 1;
  }
  return i;
}
