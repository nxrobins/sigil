// expect-fe: FE671
#[sigil::taint(x = Secret)]
pub fn f(s: i64) -> i64 { s }
