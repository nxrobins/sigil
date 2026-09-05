#[sigil::taint(s = Secret, ret = Secret)]
pub fn keep(s: i64) -> i64 {
    s
}
