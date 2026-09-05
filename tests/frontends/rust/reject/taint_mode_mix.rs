// expect-fe: FE670
#[sigil::taint(s = Secret)]
#[sigil::requires(s > 0)]
pub fn f(s: i64) -> i64 { s }
