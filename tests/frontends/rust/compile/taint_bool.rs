#[sigil::taint(b = Secret, ret = Secret)]
pub fn pick(b: bool) -> bool {
    b
}
