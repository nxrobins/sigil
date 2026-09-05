// expect-fe: FE040
// A declassify-bearing fn takes a synthesized linear cap parameter an in-subset
// call site cannot supply, so it is a leaf boundary — calling it intra-program is
// rejected before emit (SR-B5; otherwise the emitted call under-supplies the cap
// and SIGIL fails it with an arity error T070).
#[sigil::taint(s = Secret)]
fn reveal(s: i64) -> i64 {
    declassify(s)
}
pub fn caller(s: i64) -> i64 {
    reveal(s)
}
