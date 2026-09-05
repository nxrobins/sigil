// A `declassify` nested inside an arithmetic expression (SR-B10: the recognition
// walk reaches every expression position, not just a bare tail/return). The
// declassified `@Public` value composes with a literal and stays `@Public`.
#[sigil::taint(a = Secret)]
pub fn bump(a: i64) -> i64 {
    declassify(a) + 1
}
