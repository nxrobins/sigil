// expect-fe: FE040
// A @cap-bearing function may not be called intra-program in FE0 (the cap
// calling convention is deferred; anti-goal T13).
/** @cap C(deadline=2030) */
function helper(a: number): number {
  return a;
}

function f(a: number): number {
  return helper(a);
}
