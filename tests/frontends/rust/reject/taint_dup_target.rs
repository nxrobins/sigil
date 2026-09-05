// expect-fe: FE670
#[sigil::taint(s = Secret, s = Public)]
pub fn f(s: i64) -> i64 { s }
