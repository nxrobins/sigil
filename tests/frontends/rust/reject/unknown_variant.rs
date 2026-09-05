// expect-fe: FE652
enum Color { Red, Green }
pub fn f(c: Color) -> i64 {
    match c {
        Color::Red => 1,
        Color::Purple => 2,
    }
}
