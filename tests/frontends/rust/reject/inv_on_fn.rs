// expect-fe: FE660
#[sigil::invariant(x > 0)]
pub fn f(x: i64) -> i64 { x }
