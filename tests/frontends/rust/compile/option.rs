enum MyOption { Some(i64), None }
pub fn unwrap_or(o: MyOption, d: i64) -> i64 {
    match o {
        MyOption::Some(v) => v,
        MyOption::None => d,
    }
}
pub fn wrap(n: i64) -> MyOption {
    MyOption::Some(n)
}
