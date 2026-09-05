struct Inner { v: i64 }
struct Outer { inner: Inner, tag: bool }
pub fn get_v(o: Outer) -> i64 {
    return o.inner.v;
}
pub fn wrap(n: i64) -> Outer {
    return Outer { inner: Inner { v: n }, tag: true };
}
