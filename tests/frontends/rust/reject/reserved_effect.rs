// expect-fe: FE213
#[sigil::effects(Alloc)]
pub fn f(n: i64) -> i64 { return n; }
