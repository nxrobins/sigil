// expect-fe: FE030
// TS `number` is IEEE-754; a non-integer literal has no faithful i64 image
// (threat T9) and must be rejected, never silently truncated.
function f(a: number): number {
  return a + 1.5;
}
