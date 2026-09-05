// expect-fe: FE640
struct Point { x: i64, y: bool }
pub fn f(a: i64) -> Point { return Point { x: a, y: a }; }
