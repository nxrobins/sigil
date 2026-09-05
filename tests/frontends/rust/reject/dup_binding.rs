// expect-fe: FE652
enum Shape { Rect(i64, i64) }
pub fn f(s: Shape) -> i64 {
    match s {
        Shape::Rect(x, x) => x,
    }
}
