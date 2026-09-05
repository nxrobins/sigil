// expect-fe: FE652
pub fn f(n: i64) -> i64 {
    match n {
        0 => 1,
        _ if n > 5 => 2,
        _ => 3,
    }
}
