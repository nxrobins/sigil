#![no_std]
#![no_main]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
pub extern "C" fn sum_to(n: i64) -> i64 {
    let mut total: i64 = 0;
    let mut i: i64 = 1;
    while i <= n {
        total += i;
        i += 1;
    }
    total
}
