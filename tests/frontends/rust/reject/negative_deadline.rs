// expect-fe: FE612
#[sigil::cap(Net, deadline = -1)]
pub fn f(n: i64) -> i64 { return n; }
