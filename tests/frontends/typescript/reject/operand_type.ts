// expect-fe: FE311
// Relational operators require i64 operands; comparing a number to a boolean is
// rejected before emission (M7), not left to a T-code masquerade.
function f(a: number, b: boolean): boolean {
  return a < b;
}
