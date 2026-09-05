// expect-fe: FE670
#[sigil::taint(s = Secret)]
#[sigil::taint(ret = Secret)]
pub fn f(s: i64) -> i64 { s }
