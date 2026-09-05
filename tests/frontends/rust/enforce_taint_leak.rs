// The RS5a enforcement demo (DEFAULT feature set — taint checking is always-on):
// `leak` returns a `@Secret` parameter where the (default) `@Public` return is
// declared, with no `declassify` — so the trusted compiler refutes the leak with
// T001. The translator emits the `@Label` faithfully; SIGIL is the prover.
#[sigil::taint(s = Secret)]
pub fn leak(s: i64) -> i64 {
    s
}
