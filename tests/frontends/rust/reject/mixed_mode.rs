// expect-fe: FE201
#[sigil::cap(Net, deadline = 2020)]
pub fn a(n: i64) -> i64 { return n; }
#[sigil::effects(NetIO)]
pub fn b(n: i64) -> i64 { return n; }
