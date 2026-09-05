#[sigil::cap(Net, deadline = 2030)]
pub fn fetch(n: i64) -> i64 {
    return n + 1;
}
