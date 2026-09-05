// expect-fe: FE021
// An interface named a SIGIL primitive (`i64`) would emit `record i64 { ... }`,
// which the compiler silently shadows with the built-in type — so `p.x` reads as
// field access on the primitive `i64` (T122), or a value flow silently diverges
// (record vs primitive). It is rejected as a reserved type name before emission.
interface i64 {
  x: number;
}
function f(p: i64): number {
  return p.x;
}
