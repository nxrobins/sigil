// expect-fe: FE307
// Reassigning a `const` (or a parameter) is rejected (H6; SIGIL would emit T042).
function f(a: number): number {
  const x = a;
  x = 5;
  return x;
}
