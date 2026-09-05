#[sigil::requires(x > 0)]
pub fn needs_pos(x: i64) -> i64 {
    x
}
pub fn caller(n: i64) -> i64 {
    if n > 0 {
        return needs_pos(n);
    } else {
        return 0;
    }
}
