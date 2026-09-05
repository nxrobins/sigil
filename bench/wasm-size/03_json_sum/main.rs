#![no_std]
#![no_main]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn sum_n(n: i64) -> i64 {
    let mut buf: [i64; 256] = [0; 256];
    let n = n as usize;
    let n = if n > 256 { 256 } else { n };
    for (i, value) in buf.iter_mut().take(n).enumerate() {
        *value = (i as i64) + 1;
    }
    let mut total: i64 = 0;
    for value in buf.iter().take(n) {
        total += value;
    }
    total
}
