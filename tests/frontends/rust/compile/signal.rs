enum Signal { Go, Stop, Wait }
pub fn is_go(s: Signal) -> bool {
    match s {
        Signal::Go => true,
        _ => false,
    }
}
pub fn bucket(n: i64) -> i64 {
    match n {
        0 => 10,
        1 => 20,
        _ => 99,
    }
}
