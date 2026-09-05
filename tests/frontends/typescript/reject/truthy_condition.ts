// expect-fe: FE303
// SIGIL `if`/`while` require a bool condition; TS truthiness has no image (H4).
function f(n: number): number {
  if (n) {
    return 1;
  } else {
    return 0;
  }
}
