#[sigil::effects(NetIO)]
pub fn fetch(n: i64) -> i64 {
    return n + 1;
}
