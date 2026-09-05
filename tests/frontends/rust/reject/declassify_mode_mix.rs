// expect-fe: FE672
// `declassify` is taint-mode (inner ring) and does not combine with `#[sigil::cap]`
// (or effects/requires/invariant) in one file yet (SR-B6 / AG-B4-adjacent).
#[sigil::cap(NetIO, deadline = 2030)]
pub fn f(s: i64) -> i64 {
    declassify(s)
}
