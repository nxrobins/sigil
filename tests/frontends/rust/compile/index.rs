#[sigil::invariant(value >= 0)]
struct Index { value: i64 }
pub fn get(i: Index) -> i64 {
    i.value
}
pub fn zero() -> Index {
    Index { value: 0 }
}
