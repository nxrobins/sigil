// expect-fe: FE672
// `declassify` requires a scalar (`i64`/`bool`) value — `@Label` was only ever
// observed on scalars, so a struct-typed argument is rejected (SR-B2 / AG-B3).
struct P {
    x: i64,
}
pub fn f(p: P) -> i64 {
    let q = declassify(p);
    0
}
