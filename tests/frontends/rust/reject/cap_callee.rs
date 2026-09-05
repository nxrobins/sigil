// expect-fe: FE040
#[sigil::cap(Net, deadline = 2020)]
pub fn fetch(n: i64) -> i64 { return n; }
pub fn caller(n: i64) -> i64 { return fetch(n); }
