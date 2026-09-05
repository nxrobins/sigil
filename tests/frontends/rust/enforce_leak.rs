#[sigil::effects(NetIO)]
pub fn fetch(t: i64) -> i64 { return t; }
pub fn handler(a: i64) -> i64 { return fetch(a); }
