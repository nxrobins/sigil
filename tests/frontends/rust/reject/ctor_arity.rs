// expect-fe: FE652
enum MyOption { Some(i64), None }
pub fn f() -> MyOption { return MyOption::Some(1, 2); }
