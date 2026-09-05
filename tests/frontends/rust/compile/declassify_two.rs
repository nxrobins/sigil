// Two independent declassifications get two distinct linear caps (AG-B2: per-call
// provisioning, so a legitimate double-declassify stays clean rather than tripping
// O001). Each `__fe_declassify_cap_k` is consumed exactly once.
#[sigil::taint(a = Secret, b = Secret)]
pub fn two(a: i64, b: i64) -> i64 {
    let x = declassify(a);
    declassify(b)
}
