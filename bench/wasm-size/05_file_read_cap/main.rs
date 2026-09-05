#![no_std]
#![no_main]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

unsafe extern "C" {
    fn host_read_file(path_ptr: i64, path_len: i64) -> i64;
}

#[unsafe(no_mangle)]
pub extern "C" fn read_path(path_ptr: i64, path_len: i64) -> i64 {
    unsafe { host_read_file(path_ptr, path_len) }
}
