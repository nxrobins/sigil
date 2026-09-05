// RS5b enforcement (the money-shot): `declassify` launders ONLY its argument. Here
// `a` is declassified (and dropped into `x`), but the still-`@Secret` `b` is
// returned where the default `@Public` return is declared → T001. The untrusted
// translator emits both declassify and the leak faithfully; the trusted, always-on
// `taint_check` proves the un-declassified secret still cannot escape.
#[sigil::taint(a = Secret, b = Secret)]
pub fn leak2(a: i64, b: i64) -> i64 {
    let x = declassify(a);
    b
}
