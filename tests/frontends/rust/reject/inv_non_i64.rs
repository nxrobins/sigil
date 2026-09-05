// expect-fe: FE660
#[sigil::invariant(flag >= 0)]
struct S { flag: bool, n: i64 }
pub fn f(s: S) -> i64 { s.n }
