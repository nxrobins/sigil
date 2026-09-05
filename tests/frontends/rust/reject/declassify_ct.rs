// expect-fe: FE672
// `declassify_ct` (the @SecretCT constant-time declassifier) is deferred to RS5c
// (AG-B1 / SR-B3); it is never silently treated as plain `declassify`.
pub fn f(s: i64) -> i64 {
    declassify_ct(s)
}
