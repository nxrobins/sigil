enum Shape { Circle(i64), Rect(i64, i64) }
pub fn area(s: Shape) -> i64 {
    match s {
        Shape::Circle(r) => r * r * 3,
        Shape::Rect(w, h) => w * h,
    }
}
