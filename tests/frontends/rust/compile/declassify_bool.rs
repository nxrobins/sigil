// A `bool @Secret` declassified to a `@Public` bool — scalars are `i64` or `bool`
// (SR-B2); a decision computed from a secret can be revealed by authority.
#[sigil::taint(s = Secret)]
pub fn flag(s: bool) -> bool {
    declassify(s)
}
