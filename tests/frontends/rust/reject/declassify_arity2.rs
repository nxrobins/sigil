// expect-fe: FE672
// The linear `Cap<Declassify>` is frontend-synthesized, not a surface argument —
// so `declassify` accepts exactly one value, never a second operand (SR-B1).
pub fn f(a: i64, b: i64) -> i64 {
    declassify(a, b)
}
