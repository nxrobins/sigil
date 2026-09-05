// expect-fe: FE661
#[sigil::invariant(missing >= 0)]
struct S { x: i64 }
pub fn f(s: S) -> i64 { s.x }
