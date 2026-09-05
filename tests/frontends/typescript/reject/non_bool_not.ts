// expect-fe: FE309
// Unary `!` requires a bool operand; TS truthy coercion has no image (H16).
function f(a: number): boolean {
  return !a;
}
