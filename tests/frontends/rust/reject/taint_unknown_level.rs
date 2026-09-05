// expect-fe: FE670
#[sigil::taint(s = Confidential)]
pub fn f(s: i64) -> i64 { s }
