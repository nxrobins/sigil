// expect-fe: FE670
struct Point { x: i64 }
#[sigil::taint(p = Secret)]
pub fn f(p: Point) -> i64 { p.x }
