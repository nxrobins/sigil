// expect-fe: FE660
#[sigil::invariant(x == x)]
struct S { x: i64 }
pub fn f(s: S) -> i64 { s.x }
