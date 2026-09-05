// RS5b: the `declassify` escape hatch. `s` is `@Secret` and the return is the
// default `@Public` — without `declassify` this is exactly the RS5a T001 leak;
// with it, the trusted compiler accepts the downgrade (one linear cap consumed).
#[sigil::taint(s = Secret)]
pub fn reveal(s: i64) -> i64 {
    declassify(s)
}
