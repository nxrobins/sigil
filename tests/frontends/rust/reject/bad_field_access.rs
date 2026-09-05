// expect-fe: FE642
struct Point { x: i64, y: i64 }
pub fn f(p: Point) -> i64 { return p.z; }
