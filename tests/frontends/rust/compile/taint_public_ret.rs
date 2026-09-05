#[sigil::taint(a = Internal)]
pub fn ignore(a: i64) -> i64 {
    0
}
