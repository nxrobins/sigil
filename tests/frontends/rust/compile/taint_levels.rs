#[sigil::taint(a = Secret, b = Internal, ret = Secret)]
pub fn combine(a: i64, b: i64) -> i64 {
    a + b
}
