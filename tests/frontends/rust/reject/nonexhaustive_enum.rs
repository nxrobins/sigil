// expect-fe: FE651
enum Color { Red, Green, Blue }
pub fn f(c: Color) -> i64 {
    match c {
        Color::Red => 1,
        Color::Green => 2,
    }
}
