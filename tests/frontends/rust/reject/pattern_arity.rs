// expect-fe: FE652
enum MyOption { Some(i64), None }
pub fn f(o: MyOption) -> i64 {
    match o {
        MyOption::Some(a, b) => a,
        MyOption::None => 0,
    }
}
