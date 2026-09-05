//! Property fence for the record-field-offset miscompile class (#457).
//!
//! The bug: `air::lower` kept `RecordConstruct.fields` in WRITTEN order while
//! field READS use decl-order offsets, so a construct written out of decl
//! order (`R { y: b, x: a }`) stored every field at the WRONG offset and every
//! read returned silently wrong values. `record_field_order.rs` pins this with
//! hand-picked 2-field swaps.
//!
//! A 2-field swap of same-width fields can pass even with a broken offset map
//! (the two offsets coincide). This makes it a PROPERTY over the real risk
//! surface: N fields of MIXED widths, written in an ARBITRARY permutation,
//! executed — every field must read back exactly the value written for it,
//! regardless of write order. An offset-accumulation regression fails here for
//! almost every generated shape, and pinpoints the first misplaced field.

use proptest::prelude::*;
use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

/// All-correct sentinel (returned as `0 - ALL_OK`); any other trap code
/// `k` (1-based) means field `k-1` read back the wrong value.
const ALL_OK: i64 = 9999;

#[derive(Clone, Copy, Debug)]
enum FieldTy {
    I64,
    U32,
}

impl FieldTy {
    fn name(self) -> &'static str {
        match self {
            FieldTy::I64 => "i64",
            FieldTy::U32 => "u32",
        }
    }
}

/// Distinct per-field sentinel value; small + non-negative so it fits u32 and
/// stays clear of the trap-code space. Field k → 1000 + 37*k.
fn field_value(k: usize) -> i64 {
    1000 + 37 * (k as i64)
}

/// Build `record R { f0: T0, ... }` + a `tool_main` that constructs `R` with
/// fields written in `write_order`, then checks EVERY field against its
/// expected value and returns a localizing sentinel.
fn build_program(tys: &[FieldTy], write_order: &[usize]) -> String {
    let decl_fields = tys
        .iter()
        .enumerate()
        .map(|(k, t)| format!("f{k}: {}", t.name()))
        .collect::<Vec<_>>()
        .join(", ");

    let construct = write_order
        .iter()
        .map(|&k| format!("f{k}: {}", field_value(k)))
        .collect::<Vec<_>>()
        .join(", ");

    // if r.fk != Vk { return 0 - (k+1); }  — first wrong field wins.
    let mut checks = String::new();
    for k in 0..tys.len() {
        checks.push_str(&format!(
            "    if r.f{k} != {} {{ return 0 - {}; }}\n",
            field_value(k),
            k + 1
        ));
    }

    format!(
        "module tool;\n\
         record R {{ {decl_fields} }}\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n\
         \x20   let r: R = R {{ {construct} }};\n\
         {checks}    return 0 - {ALL_OK};\n\
         }}\n"
    )
}

/// Compile + run; return the negative-sentinel trap code (the
/// `record_field_order.rs` pattern).
fn run_sentinel(src: &str) -> i64 {
    let result = compile_tool(src).expect("generated record program should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a negative-sentinel return, got trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("expected negative sentinel, got a positive packed pointer"),
    }
}

proptest! {
    // Each case is a compile + wasm execution; keep the count modest.
    #![proptest_config(ProptestConfig::with_cases(120))]

    /// For any 2–6 mixed-width fields written in any permutation, every field
    /// reads back its own value.
    #[test]
    fn any_field_write_order_round_trips(
        // A vec of 2..=6 field types, then a permutation of its indices.
        tys in prop::collection::vec(
            prop_oneof![Just(FieldTy::I64), Just(FieldTy::U32)],
            2..=6,
        ),
        seed in any::<u64>(),
    ) {
        let n = tys.len();
        // Derive a permutation of 0..n from `seed` (Fisher–Yates), so proptest
        // shrinks the field-type vec while still exercising a real reordering.
        let mut order: Vec<usize> = (0..n).collect();
        let mut s = seed | 1;
        for i in (1..n).rev() {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let j = (s >> 33) as usize % (i + 1);
            order.swap(i, j);
        }

        let src = build_program(&tys, &order);
        let code = run_sentinel(&src);
        prop_assert_eq!(
            code, ALL_OK,
            "field f{} read the wrong value; types={:?} write_order={:?}",
            code - 1, tys, order
        );
    }
}

/// Anchor example: a fully-reversed 4-field mixed-width record. Explicit so a
/// reviewer sees a concrete case, and so the property isn't the only coverage.
#[test]
fn reversed_four_field_mixed_record_round_trips() {
    let tys = [FieldTy::I64, FieldTy::U32, FieldTy::I64, FieldTy::U32];
    let order = [3, 2, 1, 0];
    let code = run_sentinel(&build_program(&tys, &order));
    assert_eq!(
        code, ALL_OK,
        "reversed-order construct must round-trip every field"
    );
}

/// The property must be able to FAIL: a construct that writes decl-order values
/// still round-trips (sanity that `run_sentinel`/ALL_OK wiring is real, not
/// vacuously passing).
#[test]
fn decl_order_baseline_round_trips() {
    let tys = [FieldTy::U32, FieldTy::I64, FieldTy::U32];
    let order = [0, 1, 2];
    let code = run_sentinel(&build_program(&tys, &order));
    assert_eq!(code, ALL_OK);
}
