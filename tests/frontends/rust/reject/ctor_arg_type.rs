// expect-fe: FE630
enum MyOption { Some(i64), None }
pub fn f() -> MyOption { return MyOption::Some(true); }
