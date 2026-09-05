mod common;

use proptest::prelude::*;

use common::decode_negative_sentinel;
use common::run_returning_negative;
use common::tool_traps;

#[test]
fn negative_sentinel_decoder_rejects_non_sentinel_traps() {
    for message in [
        "",
        "wasm trap: unreachable",
        "tool returned error ()",
        "tool returned error (nope)",
        "tool returned error (42",
    ] {
        assert!(
            decode_negative_sentinel(message).is_err(),
            "unexpectedly decoded {message:?}"
        );
    }
}

#[test]
fn negative_execution_round_trips_through_the_shared_runner() {
    let source =
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - 42; }";
    assert_eq!(run_returning_negative(source), 42);
}

#[test]
fn trap_detector_distinguishes_traps_from_returns_and_negative_sentinels() {
    let trapped = "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { trap_if(true); return 1; }";
    let returned =
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 1; }";
    let sentinel =
        "module tool; pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 { return 0 - 1; }";

    assert!(tool_traps(trapped));
    assert!(!tool_traps(returned));
    assert!(!tool_traps(sentinel));
}

proptest! {
    #[test]
    fn negative_sentinel_decoder_round_trips(value in 0_i64..=i64::MAX) {
        let message = format!("tool returned error ({value})");
        prop_assert_eq!(decode_negative_sentinel(&message), Ok(value));
    }
}
