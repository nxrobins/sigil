//! Array and slice bounds checks compare an index UNSIGNED at every width (ST-2, CM1).
//!
//! The emitter picks a compare's signedness from its left operand. An 8-byte index was always
//! wrapped to u32 before its bounds check, but a 4-byte signed index reached the check as an i32,
//! where the signed `i32.ge_s` / `i32.gt_s` let a negative index through: `a[i]` read and wrote
//! before its array, `s[i]` read before its slice, and `&a[lo..hi]` built a slice that began
//! before its array. AIR now reinterprets a 4-byte signed index as u32 first
//! (`index_for_bounds_check` in `air.rs`). `str_api.rs` covers `byte_at`, the same check on a
//! string.
//!
//! Each shape runs at every index width the type checker admits. An in-bounds index must read or
//! write the right element, and every out-of-bounds index must trap. Load-bearing: a negative
//! return also reaches the host as `Trapped`, carrying the negative-return sentinel, so
//! `assert_traps` rejects that form; each out-of-bounds program also discards what it reads and
//! returns 0, so an access that does not trap comes back `Ok`. The in-bounds controls show the
//! same programs run when the index is valid.

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

mod common;

use common::{decode_negative_sentinel, run_returning_negative};

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

/// The index widths the type checker admits, each with the out-of-bounds indices that must trap
/// on a 3-element array: its length, a negative index for a signed width, and an index with the
/// top bit set.
const WIDTHS: &[(&str, &[&str])] = &[
    ("i32", &["3", "0 - 1", "0 - 2147483647"]),
    ("u32", &["3", "4294967295"]),
    ("i64", &["3", "0 - 1"]),
    ("u64", &["3"]),
];

/// The `[lo, hi)` ranges of a 3-element array that must trap, by width: a start past the end, an
/// end past the length, and for a signed width a range that starts or lies before the array.
const RANGES: &[(&str, &[(&str, &str)])] = &[
    (
        "i32",
        &[("2", "1"), ("0", "4"), ("0 - 1", "2"), ("0 - 2", "0 - 1")],
    ),
    ("u32", &[("2", "1"), ("0", "4"), ("4294967295", "2")]),
    (
        "i64",
        &[("2", "1"), ("0", "4"), ("0 - 1", "2"), ("0 - 2", "0 - 1")],
    ),
    ("u64", &[("2", "1"), ("0", "4")]),
];

/// `body` compiles and traps at run time. The negative-return sentinel is `Trapped` too, and is
/// rejected: it is a value the program returned, not a trap.
fn assert_traps(what: &str, body: &str) {
    let compiled =
        compile_tool(&tool(body)).unwrap_or_else(|e| panic!("{what} should compile: {e:?}"));
    let result = execute_ephemeral(&compiled.wasm, b"", compiled.fuel_budget, &IoGrants::none());
    let trapped = matches!(
        &result,
        Err(ToolError::Trapped { message }) if decode_negative_sentinel(message).is_err()
    );
    assert!(trapped, "{what} must trap, got {result:?}");
}

#[test]
fn array_read_traps_out_of_bounds_at_every_index_width() {
    for (ty, out_of_bounds) in WIDTHS {
        let in_bounds =
            format!("    let a: [i64; 3] = [7, 8, 9];\n    let i: {ty} = 2;\n    return 0 - a[i];");
        assert_eq!(
            run_returning_negative(&tool(&in_bounds)),
            9,
            "an in-bounds `{ty}` read"
        );
        for index in *out_of_bounds {
            assert_traps(
                &format!("an array read at a `{ty}` index of {index}"),
                &format!(
                    "    let a: [i64; 3] = [7, 8, 9];\n    let i: {ty} = {index};\n    let v: i64 = a[i];\n    return v - v;"
                ),
            );
        }
    }
}

#[test]
fn array_write_traps_out_of_bounds_at_every_index_width() {
    for (ty, out_of_bounds) in WIDTHS {
        let in_bounds = format!(
            "    let mut a: [i64; 3] = [7, 8, 9];\n    let i: {ty} = 1;\n    a[i] = 5;\n    return 0 - a[1];"
        );
        assert_eq!(
            run_returning_negative(&tool(&in_bounds)),
            5,
            "an in-bounds `{ty}` write"
        );
        for index in *out_of_bounds {
            assert_traps(
                &format!("an array write at a `{ty}` index of {index}"),
                &format!(
                    "    let mut a: [i64; 3] = [7, 8, 9];\n    let i: {ty} = {index};\n    a[i] = 5;\n    return 0;"
                ),
            );
        }
    }
}

#[test]
fn slice_read_traps_out_of_bounds_at_every_index_width() {
    for (ty, out_of_bounds) in WIDTHS {
        let in_bounds = format!(
            "    let a: [i64; 3] = [7, 8, 9];\n    let s: &[i64] = &a[0..3];\n    let i: {ty} = 2;\n    return 0 - s[i];"
        );
        assert_eq!(
            run_returning_negative(&tool(&in_bounds)),
            9,
            "an in-bounds `{ty}` read"
        );
        for index in *out_of_bounds {
            assert_traps(
                &format!("a slice read at a `{ty}` index of {index}"),
                &format!(
                    "    let a: [i64; 3] = [7, 8, 9];\n    let s: &[i64] = &a[0..3];\n    let i: {ty} = {index};\n    let v: i64 = s[i];\n    return v - v;"
                ),
            );
        }
    }
}

#[test]
fn slice_range_traps_out_of_bounds_at_every_index_width() {
    for (ty, out_of_bounds) in RANGES {
        let in_bounds = format!(
            "    let a: [i64; 3] = [7, 8, 9];\n    let lo: {ty} = 1;\n    let hi: {ty} = 3;\n    let s: &[i64] = &a[lo..hi];\n    return 0 - s[0] - s[1];"
        );
        assert_eq!(
            run_returning_negative(&tool(&in_bounds)),
            17,
            "an in-bounds `{ty}` range"
        );
        for (lo, hi) in *out_of_bounds {
            assert_traps(
                &format!("a `{ty}` slice range {lo}..{hi}"),
                &format!(
                    "    let a: [i64; 3] = [7, 8, 9];\n    let lo: {ty} = {lo};\n    let hi: {ty} = {hi};\n    let s: &[i64] = &a[lo..hi];\n    return 0;"
                ),
            );
        }
    }
}
