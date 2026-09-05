// The RS4 enforcement demo: `caller` calls `needs_pos(n)` with an UNGUARDED,
// non-literal `n` — symbolic with no preserved refinement, so the trusted compiler
// cannot establish the `x > 0` precondition → T211. The translator emits the
// `where` clause faithfully; SIGIL is the prover.
#[sigil::requires(x > 0)]
pub fn needs_pos(x: i64) -> i64 {
    x
}
pub fn caller(n: i64) -> i64 {
    needs_pos(n)
}
