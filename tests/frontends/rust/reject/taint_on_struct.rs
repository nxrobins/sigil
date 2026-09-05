// expect-fe: FE670
#[sigil::taint(x = Secret)]
struct S { x: i64 }
pub fn f(s: S) -> i64 { s.x }
