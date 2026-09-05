// expect-fe: FE660
#[sigil::requires(x < y)]
pub fn f(x: i64, y: i64) -> i64 { x }
