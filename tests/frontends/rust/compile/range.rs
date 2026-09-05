#[sigil::invariant(lo <= hi)]
struct Range { lo: i64, hi: i64 }
pub fn width(r: Range) -> i64 {
    r.hi - r.lo
}
pub fn unit() -> Range {
    Range { lo: 0, hi: 1 }
}
