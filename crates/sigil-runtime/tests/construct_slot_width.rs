//! Construct parts typed by the slot they are written to — RUNTIME value-correctness (SR-032).
//!
//! WHY THIS TEST EXISTS. A construct lays each part out at the width of the part's OWN type:
//! `lower_enum_construct` advances its payload offset by `lower_type(arg.ty).width()`, a tuple
//! goes through `flatten_record`, which does the same per element, and an array literal strides
//! by its `elem_type`. Every reader uses the width of the slot's DECLARED type instead: a `match`
//! arm reads a payload at the offsets of the variant's declared types, `let (a, b) = t` reads at
//! the offsets of the tuple type it holds, and `a[i]` steps by the declared element width. The
//! two agree only when the type checker types each part by its slot. Enum constructor arguments,
//! tuple elements, array elements and assigned values were inferred with no expected type, so an
//! integer literal there took its `i64` default (PIL N17) and a generic construct took the `i64`
//! instance. `E::V(3, 40)` for `V(i32, i64)` stored `3` as 8 bytes, and the `match` read `b` as
//! `40 << 32`. Nothing failed: the module validated and returned a plausible wrong number, which
//! is why only a value assertion catches it. A literal that did not fit its slot was not rejected
//! either: `S::V(5000000000)` for `V(i32)` compiled and stored 8 bytes into a 4-byte slot.
//!
//! WHAT IS COMPARED. Each program reads the slots back through the reader the defect broke and
//! returns `0 - value`; the harness decodes the negative sentinel, and each test asserts the
//! exact value. Each comment gives the value the compiler before the fix returned, measured on
//! the same program. The rejects are exact code sets (STYLE §4.7), each beside an accept twin
//! one edit away (§4.6), so a checker that stopped emitting the code fails too. One test reads
//! the instances the type checker registers instead: the cell size it pins is not observable
//! through a reader, since a `match` reads only the variant the tag names.
//!
//! KNOWN GAPS. The `known_gap_*` tests pin, at their measured values, the one shape of this class
//! that the fix leaves open and the defects found while testing it. Each is written to FAIL when
//! its gap closes, so the closing change updates `tests/attack/KNOWN_GAPS.md` with it.

use sigil_compiler::CompileOptions;
use sigil_compiler::air::mangle_type;
use sigil_compiler::compile_tool;
use sigil_compiler::source::SourceFile;
use sigil_compiler::type_check::Type;
use sigil_compiler::{name_resolution, parser, type_check};
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;
use sigil_test_utils::snapshot::wat_of;

/// Compile + run a full module whose `tool_main` returns `0 - K`; decode K.
fn neg(src: &str) -> i64 {
    let result = compile_tool(src).expect("module should compile");
    match execute_ephemeral(
        &result.wasm,
        b"",
        result.fuel_budget.max(1_000_000_000),
        &IoGrants::none(),
    ) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        other => panic!("expected the negative sentinel, got {other:?}"),
    }
}

/// Diagnostic codes from compiling a module, in emission order (empty = clean).
fn codes_of(src: &str) -> Vec<String> {
    match compile_tool(src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

// ── enum payloads ───────────────────────────────────────────────────────────

/// The reported reproduction, verbatim. Before the fix: 171798691840 (`40 << 32`).
#[test]
fn payload_after_a_narrow_literal_payload_reads_back_exactly() {
    let src = "module tool;
enum E { V(i32, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b) => { return b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::V(3, 40);
    return 0 - get(e);
}
";
    assert_eq!(neg(src), 40, "`b` must read 40, not the high half of `3`");
}

/// Literal-only arithmetic is a literal too. Before the fix: 171798692140.
#[test]
fn payload_after_narrow_literal_arithmetic_reads_back_exactly() {
    let src = "module tool;
enum E { V(i32, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b) => { return a.as_i64() * 100 + b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: E = E::V(1 + 2, 40);
    return 0 - get(e);
}
";
    assert_eq!(neg(src), 340);
}

/// Every payload of a variant with two narrow slots, read back. Before the fix: 708 (`b` read the
/// high half of the stored `7`, and `c` read the stored `8`).
#[test]
fn every_payload_of_a_variant_with_two_narrow_slots_reads_back_exactly() {
    let src = "module tool;
enum E { V(i32, i32, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b, c) => { return a.as_i64() * 100 + b.as_i64() * 10 + c; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(E::V(7, 8, 9));
}
";
    assert_eq!(neg(src), 789);
}

/// A bare variant constructor goes through the same slot pin as a qualified one (N14-PRB).
/// Before the fix: 171798691840.
#[test]
fn bare_variant_constructor_pins_its_payload_slots() {
    let src = "module tool;
enum E { Vv(i32, i64), Nn }
fn get(e: E) -> i64 {
    match e {
        E::Vv(a, b) => { return b; },
        E::Nn => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(Vv(3, 40));
}
";
    assert_eq!(neg(src), 40);
}

/// A `u256` payload is a pointer to a 32-byte cell; an unpinned literal was stored as an 8-byte
/// scalar in its place. Before the fix: 21474836480 (`5 << 32`).
#[test]
fn u256_payload_literal_leaves_later_payloads_intact() {
    let src = "module tool;
enum W { V(u256, i64), N }
fn get(e: W) -> i64 {
    match e {
        W::V(a, b) => { return b; },
        W::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(W::V(9, 5));
}
";
    assert_eq!(neg(src), 5);
}

/// An array literal payload is laid out at the declared element stride. Before the fix: 403
/// (`a[1]` read the high half of `4`).
#[test]
fn array_literal_payload_is_laid_out_at_the_declared_stride() {
    let src = "module tool;
enum A { V([i32; 2], i64), N }
fn get(e: A) -> i64 {
    match e {
        A::V(a, b) => {
            let x: i32 = a[0];
            let y: i32 = a[1];
            return x.as_i64() * 100 + y.as_i64() * 10 + b;
        },
        A::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(A::V([4, 5], 3));
}
";
    assert_eq!(neg(src), 453);
}

/// A tuple literal payload takes the declared element types. Before the fix: 171798691840.
#[test]
fn tuple_literal_payload_takes_the_declared_element_types() {
    let src = "module tool;
enum E { V((i32, i64)), N }
fn get(e: E) -> i64 {
    match e {
        E::V(t) => { let (a, b) = t; return b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(E::V((1, 40)));
}
";
    assert_eq!(neg(src), 40);
}

// ── generic instances: the construct is the instance its slot names ─────────

/// Before the fix the construct was `G<i64>` while the binding was `G<i32>`: 171798691840.
#[test]
fn generic_enum_under_a_let_annotation_builds_the_annotated_instance() {
    let src = "module tool;
enum G<T> { V(T, i64), N }
fn get(e: G<i32>) -> i64 {
    match e {
        G::V(a, b) => { return b; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: G<i32> = G::V(3, 40);
    return 0 - get(e);
}
";
    assert_eq!(neg(src), 40);
}

/// Before the fix: 171798691840.
#[test]
fn generic_enum_in_return_position_builds_the_declared_instance() {
    let src = "module tool;
enum G<T> { V(T, i64), N }
fn mk() -> G<i32> { return G::V(3, 40); }
fn get(e: G<i32>) -> i64 {
    match e {
        G::V(a, b) => { return b; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(mk());
}
";
    assert_eq!(neg(src), 40);
}

/// Before the fix: 171798691840.
#[test]
fn generic_enum_as_an_argument_builds_the_parameter_instance() {
    let src = "module tool;
enum G<T> { V(T, i64), N }
fn get(e: G<i32>) -> i64 {
    match e {
        G::V(a, b) => { return b; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(G::V(3, 40));
}
";
    assert_eq!(neg(src), 40);
}

/// A generic constructor nested in a payload builds the payload's instance. Before the fix:
/// 171798691840.
#[test]
fn generic_enum_nested_in_a_payload_builds_the_payload_instance() {
    let src = "module tool;
enum P<X> { Two(X, i64) }
enum E { V(P<i32>), N }
fn inner(p: P<i32>) -> i64 {
    match p {
        P::Two(a, b) => { return b; },
    }
    return 0;
}
fn get(e: E) -> i64 {
    match e {
        E::V(p) => { return inner(p); },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(E::V(P::Two(3, 40)));
}
";
    assert_eq!(neg(src), 40);
}

/// With no instance in view, a generic enum's concretely declared slot is still pinned; the
/// type parameter is inferred from its argument. Before the fix: 171798691840.
#[test]
fn concrete_slot_of_an_unannotated_generic_enum_is_pinned() {
    let src = "module tool;
enum B<T> { V(T, i32, i64), N }
fn get(e: B<bool>) -> i64 {
    match e {
        B::V(a, c, b) => { return b; },
        B::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(B::V(true, 7, 40));
}
";
    assert_eq!(neg(src), 40);
}

/// The place is the slot of an assignment. Before the fix: 171798691840.
#[test]
fn generic_enum_assigned_to_a_place_builds_the_place_instance() {
    let src = "module tool;
enum G<T> { V(T, i64), N }
fn get(e: G<i32>) -> i64 {
    match e {
        G::V(a, b) => { return b; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut g: G<i32> = G::N;
    g = G::V(3, 40);
    return 0 - get(g);
}
";
    assert_eq!(neg(src), 40);
}

/// A bare unit variant takes the instance of the slot it is written to (GAP 2 now sees the
/// payload slot). Before the fix this was rejected: the unit variant typed as the argless `M`.
#[test]
fn bare_unit_variant_payload_takes_the_slot_instance() {
    let src = "module tool;
enum M<T> { Jj(T), Nn }
enum E { V(M<i64>, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(m, b) => { return b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(E::V(Nn, 40));
}
";
    assert_eq!(neg(src), 40);
}

/// The instances of the generic enum `name` that type-checking `src` registers, by mangled name.
fn registered_instances(src: &str, name: &str) -> Vec<String> {
    let source = SourceFile::new("<construct-slot-width>", src);
    let (ast, parse_diagnostics) = parser::parse(&source);
    assert!(parse_diagnostics.is_empty(), "the program must parse");
    let resolved = name_resolution::resolve(&ast).expect("the program must resolve");
    let (typed, _) = type_check::check_with_options(&resolved, &CompileOptions::default())
        .unwrap_or_else(|_| panic!("the program must type-check"));
    typed
        .enums
        .keys()
        .filter(|key| key.starts_with(name) && key.as_str() != name)
        .cloned()
        .collect()
}

/// A type parameter that no payload binds takes the expected instance's argument, as a unit
/// variant's parameters do. It used to become `Type::Error`, which lowers to zero width. Before
/// the fix this registered `Either__i64$error` (the literal at its `i64` default, `B` unbound);
/// with the payload typed but `B` still unbound it registered `Either__i32$error`, an 8-byte cell
/// where the instance its readers use, `Either<i32, i64>`, is 12 bytes.
#[test]
fn unbound_type_parameter_takes_the_expected_instance() {
    let src = "module tool;
enum Either<A, B> { L(A), R(B), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: Either<i32, i64> = Either::L(7);
    return input_len;
}
";
    let instance = mangle_type(&Type::Named("Either".into(), vec![Type::I32, Type::I64]));
    assert_eq!(registered_instances(src, "Either"), vec![instance]);
}

// ── tuple elements ──────────────────────────────────────────────────────────

/// The reported tuple-array shape. Before the fix: 103 (`a[1]` read the high half of `1`).
#[test]
fn narrow_array_in_a_tuple_reads_back_exactly() {
    let src = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let t: ([i32; 2], i64) = ([1, 2], 3);
    let (a, b) = t;
    let x: i32 = a[0];
    let y: i32 = a[1];
    return 0 - (x.as_i64() * 100 + y.as_i64() * 10 + b);
}
";
    assert_eq!(neg(src), 123);
}

/// Before the fix: 171798691940.
#[test]
fn narrow_tuple_element_under_a_let_annotation_reads_back() {
    let src = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let t: (i32, i64) = (1, 40);
    let (a, b) = t;
    return 0 - (a.as_i64() * 100 + b);
}
";
    assert_eq!(neg(src), 140);
}

/// Before the fix: 171798691940.
#[test]
fn narrow_tuple_element_in_return_position_reads_back() {
    let src = "module tool;
fn mk() -> (i32, i64) { return (1, 40); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let (a, b) = mk();
    return 0 - (a.as_i64() * 100 + b);
}
";
    assert_eq!(neg(src), 140);
}

/// Before the fix: 171798691940.
#[test]
fn narrow_tuple_element_as_an_argument_reads_back() {
    let src = "module tool;
fn get(p: (i32, i64)) -> i64 { let (a, b) = p; return a.as_i64() * 100 + b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get((1, 40));
}
";
    assert_eq!(neg(src), 140);
}

/// Before the fix: 171798691940.
#[test]
fn narrow_tuple_element_in_a_record_field_reads_back() {
    let src = "module tool;
record R { t: (i32, i64) }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let r: R = R { t: (1, 40) };
    let (a, b) = r.t;
    return 0 - (a.as_i64() * 100 + b);
}
";
    assert_eq!(neg(src), 140);
}

/// Before the fix: 171798691940.
#[test]
fn narrow_tuple_assigned_to_a_place_reads_back() {
    let src = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut t: (i32, i64) = (0, 0);
    t = (1, 40);
    let (a, b) = t;
    return 0 - (a.as_i64() * 100 + b);
}
";
    assert_eq!(neg(src), 140);
}

// ── array elements ──────────────────────────────────────────────────────────

/// Before the fix: 85899346120.
#[test]
fn array_of_narrow_tuples_reads_back() {
    let src = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let arr: [(i32, i64); 2] = [(1, 10), (2, 20)];
    let (a, b) = arr[1];
    return 0 - (a.as_i64() * 100 + b);
}
";
    assert_eq!(neg(src), 220);
}

/// Before the fix: 171798691840.
#[test]
fn array_of_generic_enums_builds_the_element_instance() {
    let src = "module tool;
enum G<T> { V(T, i64), N }
fn get(e: G<i32>) -> i64 {
    match e {
        G::V(a, b) => { return b; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let arr: [G<i32>; 1] = [G::V(3, 40)];
    return 0 - get(arr[0]);
}
";
    assert_eq!(neg(src), 40);
}

/// Before the fix this was rejected: the bare unit variant, element 0, typed as the argless `M`,
/// so element 1 failed the homogeneity check.
#[test]
fn bare_unit_variant_element_takes_the_element_instance() {
    let src = "module tool;
enum M<T> { Jj(T), Nn }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: [M<i64>; 2] = [Nn, Jj(7)];
    match a[1] {
        M::Jj(x) => { return 0 - x; },
        M::Nn => { return 0 - 1; },
    }
    return 0;
}
";
    assert_eq!(neg(src), 7);
}

// ── literals that do not fit a payload slot are rejected ────────────────────

/// Before the fix this compiled and stored 8 bytes into the 4-byte slot. The accept twin is the
/// largest `i32`.
#[test]
fn payload_literal_out_of_range_for_its_slot_is_rejected() {
    let module = |lit: &str| {
        format!(
            "module tool;
enum S {{ V(i32, i64), N }}
fn get(e: S) -> i64 {{
    match e {{
        S::V(a, b) => {{ return a.as_i64() + b; }},
        S::N => {{ return 0; }},
    }}
    return 0;
}}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    return 0 - get(S::V({lit}, 1));
}}
"
        )
    };
    assert_eq!(codes_of(&module("2147483648")), vec!["T071"]);
    assert_eq!(neg(&module("2147483647")), 2147483648);
}

/// SIGIL does not convert an integer literal to `f64`; before the fix it compiled and stored the
/// literal's `i64` bits in the `f64` slot. The accept twin writes a float literal.
#[test]
fn integer_literal_for_a_float_payload_is_rejected() {
    let module = |lit: &str| {
        format!(
            "module tool;
enum F {{ V(f64), N }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let f: F = F::V({lit});
    return 0 - 1;
}}
"
        )
    };
    assert_eq!(codes_of(&module("3")), vec!["T071"]);
    assert_eq!(neg(&module("3.0")), 1);
}

/// An overflowing literal leaf inside payload arithmetic is rejected like a top-level one: every
/// leaf must fit the slot (N20-PIL), so `0 - 2147483648` is rejected although its value would
/// fit. The accept twin's leaf is the largest `i32`.
#[test]
fn payload_arithmetic_with_an_out_of_range_leaf_is_rejected() {
    let module = |rhs: &str| {
        format!(
            "module tool;
enum S {{ V(i32), N }}
fn get(e: S) -> i64 {{
    match e {{
        S::V(a) => {{ return a.as_i64(); }},
        S::N => {{ return 0; }},
    }}
    return 0;
}}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    return 0 - (get(S::V(0 - {rhs})) + 2147483648);
}}
"
        )
    };
    assert_eq!(codes_of(&module("2147483648")), vec!["T071"]);
    assert_eq!(neg(&module("2147483647")), 1);
}

// ── the slot type reaches arithmetic: an unsigned payload divides unsigned ──

/// `10 / 3` in a `u64` slot is a `u64` division. The value is the same either way for these
/// operands, so the evidence is the emitted opcode: before the fix the literals defaulted to
/// `i64` and the module divided with `i64.div_s`. The absence check is shown to detect a planted
/// signed division first (SC-P4): the same program over an `i64` payload must emit `i64.div_s`.
#[test]
fn unsigned_payload_arithmetic_divides_unsigned() {
    let signed = "module tool;
enum S { V(i64), N }
fn get(e: S) -> i64 {
    match e {
        S::V(a) => { return a; },
        S::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i64 = get(S::V(10 / 3));
    return 0 - 1;
}
";
    let planted = wat_of(&compile_tool(signed).expect("module should compile").wasm);
    assert!(
        planted.contains("i64.div_s"),
        "anti-stub: the detector must see the signed division an `i64` payload plants"
    );
    let src = "module tool;
enum U { V(u64), N }
fn get(e: U) -> u64 {
    match e {
        U::V(a) => { return a; },
        U::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: u64 = get(U::V(10 / 3));
    return 0 - 1;
}
";
    let wat = wat_of(&compile_tool(src).expect("module should compile").wasm);
    assert!(
        wat.contains("i64.div_u"),
        "the payload's division must be unsigned"
    );
    assert!(
        !wat.contains("i64.div_s"),
        "no signed division may remain in the module"
    );
}

// ── a generic function's and a closure's arguments ──────────────────────────

/// A generic function's concrete parameter is a slot like a resolved function's. No argument of a
/// generic function was pinned, so the tuple was laid out as `(i64, i64)` and the instance read
/// `y` from the wrong bytes. Before the fix: 171798691940.
#[test]
fn generic_function_tuple_argument_takes_the_parameter_types() {
    let src = "module tool;
fn g<T>(a: T, t: (i32, i64)) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - g(true, (1, 40));
}
";
    assert_eq!(neg(src), 140);
}

/// The generic-enum instance a generic function's parameter names. Before the fix: 171798692140.
#[test]
fn generic_function_enum_argument_builds_the_parameter_instance() {
    let src = "module tool;
enum G<T> { V(T, i64), N }
fn g<U>(a: U, e: G<i32>) -> i64 {
    match e {
        G::V(x, y) => { return x.as_i64() * 100 + y; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - g(true, G::V(3, 40));
}
";
    assert_eq!(neg(src), 340);
}

/// An array literal written to a generic function's `[i32; 2]` parameter is laid out at a
/// 4-byte stride. Before the fix: 10.
#[test]
fn generic_function_array_argument_takes_the_parameter_stride() {
    let src = "module tool;
fn g<T>(a: T, arr: [i32; 2]) -> i64 {
    return arr[0].as_i64() * 10 + arr[1].as_i64();
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - g(true, [1, 2]);
}
";
    assert_eq!(neg(src), 12);
}

/// A parameter that mentions a type parameter is pinned once an earlier argument has bound it:
/// `a: T` binds `T = i64` before `t: (i32, T)` is inferred. Before the fix: 30064771472.
#[test]
fn generic_function_argument_after_its_binding_takes_the_instance_types() {
    let src = "module tool;
fn g<T>(a: T, t: (i32, T)) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: i64 = 0;
    return 0 - g(a, (4, 7));
}
";
    assert_eq!(neg(src), 407);
}

/// A type parameter that only a LATER argument binds: the tuple was inferred with no slot, and is
/// narrowed once the instance is known. Before the fix: 30064771472.
#[test]
fn generic_function_argument_bound_by_a_later_argument_is_narrowed() {
    let src = "module tool;
fn g<T>(t: (i32, T), a: T) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: i64 = 0;
    return 0 - g((4, 7), a);
}
";
    assert_eq!(neg(src), 407);
}

/// A type parameter that only a literal binds: the instance is `g<i64>`, as the literal defaults,
/// and the tuple is narrowed to its `(i32, i64)` parameter. Before the fix: 30064771472.
#[test]
fn generic_function_argument_bound_only_by_a_literal_is_narrowed() {
    let src = "module tool;
fn g<T>(a: T, t: (i32, T)) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - g(0, (4, 7));
}
";
    assert_eq!(neg(src), 407);
}

/// A type parameter bound inside the argument itself: `y: i32` binds `T`, and the `5` beside it
/// takes `T` too. Before the fix: 17179869534.
#[test]
fn generic_function_argument_bound_inside_itself_is_narrowed() {
    let src = "module tool;
fn g<T>(t: (T, T, i64)) -> i64 {
    let (a, b, c) = t;
    return a.as_i64() * 100 + b.as_i64() * 10 + c;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let y: i32 = 3;
    return 0 - g((y, 5, 4));
}
";
    assert_eq!(neg(src), 354);
}

/// A turbofish names the instance before any argument is inferred, so every argument is pinned.
/// Before the fix: 171798691940.
#[test]
fn generic_function_turbofish_argument_takes_the_parameter_types() {
    let src = "module tool;
fn g<T>(a: T, t: (i32, i64)) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - g::<bool>(true, (1, 40));
}
";
    assert_eq!(neg(src), 140);
}

/// A generic call had no argument check: an argument that does not fit its concrete parameter
/// compiled and the instance read it at the parameter's offsets. Each is now the resolved call's
/// T071; the twin that fits reads back. Before the fix the three compiled, returning 171798691940,
/// 4294967996 and 74798237697.
#[test]
fn generic_function_argument_that_does_not_fit_its_parameter_is_rejected() {
    let template = "module tool;
fn g<T>(a: T, t: (i32, i64)) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let t: TUPLE = (1, 40);
    let x: i64 = 7;
    return 0 - g(true, ARG);
}
";
    let src = |tuple: &str, arg: &str| template.replace("TUPLE", tuple).replace("ARG", arg);
    assert_eq!(codes_of(&src("(i64, i64)", "t")), vec!["T071"]);
    assert_eq!(codes_of(&src("(i32, i64)", "(x, 1)")), vec!["T071"]);
    assert_eq!(
        codes_of(&src("(i32, i64)", "(5000000000, 1)")),
        vec!["T071"]
    );
    assert_eq!(neg(&src("(i32, i64)", "t")), 140);
}

/// A closure-typed local's arguments are pinned to its parameter types, as a function's are.
/// Before the fix: 171798691940.
#[test]
fn closure_argument_takes_the_parameter_types() {
    let src = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let f = fn(t: (i32, i64)) -> i64 { let (x, y) = t; return x.as_i64() * 100 + y; };
    return 0 - f((1, 40));
}
";
    assert_eq!(neg(src), 140);
}

/// A bare unit variant typed without type arguments (no slot names its instance) fits the generic
/// enum parameter it is passed to: its cell holds only the tag. The argument check of the previous
/// change rejected it (T071, "expected `Option<i64>`, found `Option`"), though it returned 5.
#[test]
fn generic_function_argless_unit_variant_argument_fits_the_instance() {
    let src = "module tool;
fn or_default<T>(o: Option<T>, d: T) -> T {
    match o {
        Some(v) => { return v; },
        None => { return d; },
    }
    return d;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - or_default(None, 5);
}
";
    assert_eq!(neg(src), 5);
}

/// A literal that does not fit its slot inside a compound argument narrowed after inference is
/// T071, as at a scalar slot. Before, the sum was narrowed to `i32` around an `i64` leaf (a module
/// the engine refused, or 100568041573 before the previous change), and an array literal's
/// element likewise; the twin that fits reads back.
#[test]
fn literal_out_of_range_inside_a_compound_argument_is_rejected() {
    let tuple = "module tool;
fn g<T>(t: (i32, T), a: T) -> i64 {
    let (x, y) = t;
    return x.as_i64() * 100 + y;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: i64 = 0;
    return 0 - g((1 + LEAF, 7), a);
}
";
    let array = "module tool;
fn f(arr: [i32; 1]) -> i64 { return arr[0].as_i64(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - f([1 + 5000000000]);
}
";
    assert_eq!(codes_of(&tuple.replace("LEAF", "5000000000")), vec!["T071"]);
    assert_eq!(codes_of(array), vec!["T071"]);
    assert_eq!(neg(&tuple.replace("LEAF", "5")), 607);
}

/// A closure passed to a generic function's function-typed parameter was checked for its effect
/// row only. One taking an `i64` for `Fn(i32) -> T` compiled and trapped at the call; one taking a
/// `(i64, i64)` for `Fn((i32, i64)) -> T` ran, reading its pinned `(i32, i64)` argument at other
/// offsets (17179869184100; on main both sides used `i64` widths and it returned 140 by accident).
/// Each is now T071; the closure with the parameter's types reads back.
#[test]
fn generic_closure_argument_types_are_checked() {
    let scalar = "module tool;
fn apply<T>(f: Fn(i32) -> T, x: i32) -> T { return f(x); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(a: PARAM) -> i64 { return 0 + 1; };
    return 0 - apply(c, 5);
}
";
    let tuple = "module tool;
fn apply<T>(f: Fn((i32, i64)) -> T, t: (i32, i64)) -> T { return f(t); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(p: PARAM) -> i64 { let (a, b) = p; return a.as_i64() * 100 + b; };
    return 0 - apply(c, (1, 40));
}
";
    assert_eq!(codes_of(&scalar.replace("PARAM", "i64")), vec!["T071"]);
    assert_eq!(
        codes_of(
            &tuple
                .replace("PARAM", "(i64, i64)")
                .replace("a.as_i64()", "a")
        ),
        vec!["T071"]
    );
    assert_eq!(neg(&scalar.replace("PARAM", "i32")), 1);
    assert_eq!(neg(&tuple.replace("PARAM", "(i32, i64)")), 140);
}

/// The generic argument check reports only a value stored otherwise than the instance reads it. A
/// `u64` passed where a literal bound the parameter, so that the literal's `i64` instance reads it
/// (X-M7), is stored alike, and so is a bare `None` typed without arguments: at the top, inside a
/// tuple, bound to a local, or passed in to a closure that reads an `Option<i64>`. Main passed
/// each as it is and returned these values. The fourth review's type check rejected the first
/// five (T071), and the closure check that replaced it rejected the last, since it compared the
/// closure's parameter the wrong way round.
#[test]
fn generic_argument_of_the_same_representation_is_accepted() {
    let max = "module tool;
fn max<T>(a: T, b: T) -> T { if a > b { return a; } return b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n: u64 = 7;
    let m: u64 = max(0, n);
    return 0 - m.as_i64();
}
";
    let first = "module tool;
fn first<T>(a: T, b: T) -> T { return a; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n: u64 = 7;
    let m: u64 = first(n, 5);
    let k: u64 = first(5, n);
    return 0 - (m.as_i64() * 10 + k.as_i64());
}
";
    let tuple = "module tool;
fn snd<T>(a: T, b: T) -> T { return b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let p: (u64, u64) = (3, 4);
    let q: (u64, u64) = snd((1, 2), p);
    let (a, b) = q;
    return 0 - (a.as_i64() * 10 + b.as_i64());
}
";
    let none_in_tuple = "module tool;
fn g<T>(p: (Option<T>, T)) -> T {
    let (o, d) = p;
    match o {
        Some(v) => { return v; },
        None => { return d; },
    }
    return d;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - g((None, 5));
}
";
    let none_local = "module tool;
fn or_default<T>(o: Option<T>, d: T) -> T {
    match o {
        Some(v) => { return v; },
        None => { return d; },
    }
    return d;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let o = None;
    return 0 - or_default(o, 5);
}
";
    let none_to_closure = "module tool;
fn apply<T>(x: T, f: Fn(T) -> i64) -> i64 { return f(x); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(o: Option<i64>) -> i64 {
        match o {
            Some(v) => { return v; },
            None => { return 7; },
        }
        return 0;
    };
    return 0 - apply(None, c);
}
";
    assert_eq!(neg(max), 7);
    assert_eq!(neg(first), 75);
    assert_eq!(neg(tuple), 34);
    assert_eq!(neg(none_in_tuple), 5);
    assert_eq!(neg(none_local), 5);
    assert_eq!(neg(none_to_closure), 7);
}

/// A difference in signedness passes only where a literal bound the type parameter. Where a
/// concrete argument bound it, a value of the other signedness fits no typing of the call, and it
/// is T071: `max(a, b)` with `a: u32` and `b: i32` compiled, its instance reading the `i32` as a
/// `u32`, and so did `g(a, (5, n, 6))` with `a: i64` and `n: u64`, whose tuple main laid out at
/// the default widths (300647711220). With `b: u32`, or `a: u64`, the call fits, and the literals
/// beside the `u64` are narrowed to the instance's `i32` parts.
#[test]
fn generic_argument_of_the_other_signedness_fits_only_a_literal_binding() {
    let max = "module tool;
fn max<T>(a: T, b: T) -> T { if a > b { return a; } return b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: u32 = 1;
    let b: TYPE = 3;
    let r: u32 = max(a, b);
    return 0 - r.as_i64();
}
";
    let mixed = "module tool;
fn g<T>(a: T, t: (i32, T, i32)) -> i64 {
    let (x, y, z) = t;
    return x.as_i64() * 100 + y.as_i64() * 10 + z.as_i64();
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a: TYPE = 0;
    let n: u64 = 7;
    return 0 - g(a, (5, n, 6));
}
";
    assert_eq!(codes_of(&max.replace("TYPE", "i32")), vec!["T071"]);
    assert_eq!(codes_of(&mixed.replace("TYPE", "i64")), vec!["T071"]);
    assert_eq!(neg(&max.replace("TYPE", "u32")), 3);
    assert_eq!(neg(&mixed.replace("TYPE", "u64")), 576);
}

/// A closure inside a generic construct is checked as one at the top level is: inside a generic
/// function's tuple or `Option` argument, a generic record's field (inferred or annotated), or a
/// generic enum's payload. The instance passes the closure's arguments in, so a closure's own
/// parameter type is the slot they must fit. Each misfit here compiled and read its `(i32, i64)`
/// argument at `(i64, i64)` offsets, returning 171798691841 once the argument was laid out at its
/// slot's widths (main returned 1, as it laid the argument out at the default widths too). Each
/// is now T071; the closure with the slot's parameter types reads back 1.
#[test]
fn closure_inside_a_generic_construct_is_checked() {
    let tuple = "module tool;
fn apply<T>(p: (Fn((i32, i64)) -> T, i64), t: (i32, i64)) -> T {
    let (f, k) = p;
    return f(t);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(q: PARAM) -> i64 { let (a, b) = q; return a.as_i64(); };
    return 0 - apply((c, 0), (1, 40));
}
";
    let option = "module tool;
fn run<T>(o: Option<Fn((i32, i64)) -> T>, t: (i32, i64), d: T) -> T {
    match o {
        Some(f) => { return f(t); },
        None => { return d; },
    }
    return d;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(q: PARAM) -> i64 { let (a, b) = q; return a.as_i64(); };
    return 0 - run(Some(c), (1, 40), 0);
}
";
    let field = "module tool;
record Holder<T> { f: Fn((i32, i64)) -> T }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(q: PARAM) -> i64 { let (a, b) = q; return a.as_i64(); };
    let h BINDING = Holder { f: c };
    let g = h.f;
    let t: (i32, i64) = (1, 40);
    return 0 - g(t);
}
";
    let payload = "module tool;
enum K<T> { V(Fn((i32, i64)) -> T), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(q: PARAM) -> i64 { let (a, b) = q; return a.as_i64(); };
    let k: K<i64> = K::V(c);
    let t: (i32, i64) = (1, 40);
    match k {
        K::V(f) => { return 0 - f(t); },
        K::N => { return 0; },
    }
    return 0;
}
";
    let inferred = field.replace("BINDING", "");
    let annotated = field.replace("BINDING", ": Holder<i64>");
    for template in [tuple, option, &inferred, &annotated, payload] {
        let misfit = template.replace("PARAM", "(i64, i64)");
        assert_eq!(codes_of(&misfit), vec!["T071"], "{misfit}");
        let fit = template.replace("PARAM", "(i32, i64)");
        assert_eq!(neg(&fit), 1, "{fit}");
    }
}

/// A generic argument whose parameter type mentions a function type is inferred with no slot (a
/// closure in it binds a row variable that a slot would preempt), so the literals beside the
/// closure kept the `i64` default: `g((c, (1, 40)), 0)` for `p: (Fn(i64) -> i64, (i32, i64))` laid
/// the inner tuple out as `(i64, i64)` and returned 171798691940. They are narrowed once the
/// instance is known, as any argument's literals are.
#[test]
fn literal_beside_a_closure_in_a_generic_argument_is_narrowed() {
    let src = "module tool;
fn g<T>(p: (Fn(i64) -> i64, (i32, i64)), x: T) -> i64 {
    let (f, t) = p;
    let (a, b) = t;
    return f(a.as_i64() * 100 + b);
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(v: i64) -> i64 { return v; };
    return 0 - g((c, (1, 40)), 0);
}
";
    assert_eq!(neg(src), 140);
}

/// A generic record's field whose declared type mentions a type parameter was pinned only under an
/// annotation that names the instance. Built without one, it kept the widths it was typed with:
/// `P { t: (1, 40) }` for `record P<T> { t: (i32, T) }` laid the tuple out as `(i64, i64)`, and the
/// read of `p.t` returned 171798691940, whether the field itself or another field bound `T`. It is
/// now fitted to the instance once the construction's bindings are known.
#[test]
fn generic_record_field_is_fitted_to_the_instance() {
    let own = "module tool;
record P<T> { t: (i32, T) }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let p = P { t: (1, 40) };
    let q = p.t;
    let (a, b) = q;
    return 0 - (a.as_i64() * 100 + b);
}
";
    let other = "module tool;
record P<T> { t: (i32, T), u: T }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let k: i64 = 0;
    let p = P { t: (1, 40), u: k };
    let q = p.t;
    let (a, b) = q;
    return 0 - (a.as_i64() * 100 + b + p.u);
}
";
    assert_eq!(neg(own), 140);
    assert_eq!(neg(other), 140);
}

/// A part of a generic record's field that the instance does not read alike is T071, as a concrete
/// field's mismatch is. A `bool` in the `i32` part compiled without a diagnostic. A `u32` field
/// beside a literal that bound `T` first builds the literal's `i64` instance, as a generic call
/// does (X-M7), so the 4-byte value sat in an 8-byte field and `p.b` read 4 bytes past it. Main
/// returned 7 here only because those bytes were still zero: with another `Pair` built after it,
/// `p.b` took that `Pair`'s first bytes as its high half. The twin with the `u32` first builds
/// `Pair<u32>`, and its literal is narrowed to it.
#[test]
fn generic_record_field_the_instance_does_not_read_alike_is_rejected() {
    let bool_part = "module tool;
record P<T> { t: (i32, T) }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let p = P { t: (true, 40) };
    return 0 - 1;
}
";
    let literal_first = "module tool;
record Pair<T> { a: T, b: T }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n: u32 = 7;
    let p = Pair { a: 5, b: n };
    return 0 - p.b;
}
";
    let concrete_first = "module tool;
record Pair<T> { a: T, b: T }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n: u32 = 7;
    let p = Pair { a: n, b: 5 };
    let x: u32 = p.b;
    return 0 - (p.a.as_i64() * 10 + x.as_i64());
}
";
    // Unlike a generic call, a record does not let a concrete type nested in a later field replace
    // a literal's binding: `f(5, s)` for `f<T>(a: T, o: Option<T>)` builds `f<i32>`.
    let nested_after = "module tool;
record R<T> { a: T, o: Option<T> }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 5;
    let s: Option<i32> = Some(x);
    let r = R { a: 5, o: s };
    return 0 - 1;
}
";
    assert_eq!(codes_of(bool_part), vec!["T071"]);
    assert_eq!(codes_of(literal_first), vec!["T071"]);
    assert_eq!(codes_of(nested_after), vec!["T071"]);
    assert_eq!(neg(concrete_first), 75);
}

/// The same for a generic enum's payload: built with no expected instance, `B::V((1, 40))` for
/// `V((i32, T))` laid the tuple out as `(i64, i64)`, and the `match` returned 171798691940. Under a
/// slot that names the instance it was already pinned.
#[test]
fn generic_enum_payload_is_fitted_to_the_instance() {
    let src = "module tool;
enum B<T> { V((i32, T)), N }
fn get(b: B<i64>) -> i64 {
    match b {
        B::V(q) => { let (a, c) = q; return a.as_i64() * 100 + c; },
        B::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let b = B::V((1, 40));
    return 0 - get(b);
}
";
    assert_eq!(neg(src), 140);
}

/// A closure's parameter and return annotations are held to the arity rule every other written
/// type is held to (T231). Resolved raw, `fn(o: Option) -> i64` typed a value that may carry a
/// payload as an enum without type arguments, which a generic call accepts in any instance's place
/// as a tag-only cell: `or_default(o, 7)` inside, given a `Some(5)` built as an `Option<i32>`, read
/// the 4-byte payload as 8 bytes and returned 4294967301. It is T231 now, with T071 for the closure
/// argument whose parameter is that type; the closure annotated `Option<i32>` reads back.
#[test]
fn closure_annotation_without_type_arguments_is_rejected() {
    let template = "module tool;
fn apply<T>(x: T, f: Fn(T) -> i64) -> i64 { return f(x); }
fn or_default<T>(o: Option<T>, d: T) -> T {
    match o {
        Some(v) => { return v; },
        None => { return d; },
    }
    return d;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 5;
    let s: Option<i32> = Some(x);
    let c = fn(o: OPTION) -> i64 { return or_default(o, 7).as_i64(); };
    return 0 - apply(s, c);
}
";
    let ret = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(v: i64) -> Option { return None; };
    return 0 - 1;
}
";
    assert_eq!(
        codes_of(&template.replace("OPTION", "Option")),
        vec!["T231", "T071"]
    );
    assert_eq!(codes_of(ret), vec!["T231"]);
    assert_eq!(neg(&template.replace("OPTION", "Option<i32>")), 5);
}

/// A generic construct's part is pinned once the parts written before it bind the type
/// parameters its type mentions, as a generic function's argument is. Before, a generic record's
/// field or a generic enum's payload was pinned only under an annotation that names the instance,
/// so an inline `Some(5)` in `R { a: x, o: Some(5) }` for `record R<T> { a: T, o: Option<T> }`
/// with `x: i32` was built at `Option<i64>`; main read it back as 5 only because the narrow part
/// was the cell's last, and the previous change rejected it (T071). With the part that binds `T`
/// written after it, the `Some` is still built before `T` is known, so it is still T071, as the
/// same order is for a generic call.
#[test]
fn generic_construct_part_is_pinned_once_earlier_parts_bind_it() {
    let get = "fn get(o: Option<i32>) -> i64 {
    match o {
        Some(v) => { return v.as_i64(); },
        None => { return 0; },
    }
    return 0;
}
";
    let record = format!(
        "module tool;
record R<T> {{ a: T, o: Option<T> }}
{get}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let x: i32 = 2;
    let r = R {{ FIELDS }};
    return 0 - get(r.o);
}}
"
    );
    let payload = format!(
        "module tool;
enum E<T> {{ V(T, Option<T>), N }}
{get}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let x: i32 = 2;
    let e = E::V(x, Some(5));
    match e {{
        E::V(a, o) => {{ return 0 - get(o); }},
        E::N => {{ return 0; }},
    }}
    return 0;
}}
"
    );
    let payload_first = "module tool;
enum F<T> { V(Option<T>, T), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 2;
    let e = F::V(Some(5), x);
    return 0 - 1;
}
";
    assert_eq!(neg(&record.replace("FIELDS", "a: x, o: Some(5)")), 5);
    assert_eq!(
        codes_of(&record.replace("FIELDS", "o: Some(5), a: x")),
        vec!["T071"]
    );
    assert_eq!(neg(&payload), 5);
    assert_eq!(codes_of(payload_first), vec!["T071"]);
}

/// A generic enum's payload whose type parameter a literal bound first is read by the literal's
/// `i64` instance, as a generic call's argument and a generic record's field are (X-M7), so an
/// `i32` beside it does not fit its 8-byte slot: `PE::P(5, x)` is T071. Main read it back as 57
/// only because the cell is allocated at the instance's size and the slot's high bytes were still
/// zero. With the `i32` first, `T` is `i32` and the literal is pinned to it.
#[test]
fn literal_first_generic_enum_payload_is_rejected() {
    let template = "module tool;
enum PE<T> { P(T, T), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 7;
    let e = PE::P(ARGS);
    match e {
        PE::P(a, b) => { return 0 - (a.as_i64() * 10 + b.as_i64()); },
        PE::N => { return 0; },
    }
    return 0;
}
";
    assert_eq!(codes_of(&template.replace("ARGS", "5, x")), vec!["T071"]);
    assert_eq!(neg(&template.replace("ARGS", "x, 5")), 75);
}

/// A generic enum's payload whose type holds a function type is pinned like any other payload. A
/// generic function leaves such a slot unpinned, since a closure's effect row binds the function's
/// row variable, and that filter also reached a generic enum with no instance in view, which binds
/// no row variable (E011). So `W::F((1, 40, f), 7)` for `F((i32, i64, Fn(i64) -> i64), T)` laid the
/// tuple out as `(i64, i64, _)` and read 171798691940, an `[i32; 2]` beside a closure read 10, and
/// a bare `None` in an `Option<Fn(i64) -> i64>` payload was T071, all as on main. An earlier step
/// of this change pinned the three by the payload types, and the progressive pin had dropped them.
#[test]
fn function_typed_payload_of_a_generic_enum_is_pinned() {
    let program = |payload: &str, construct: &str, read: &str| {
        format!(
            "module tool;
enum W<T> {{ F({payload}, T), N }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let f = fn(x: i64) -> i64 {{ return x; }};
    let w = W::F({construct}, 7);
    match w {{
        W::F(t, k) => {{
{read}
        }},
        W::N => {{ return 0; }},
    }}
    return 0;
}}
"
        )
    };
    let tuple = program(
        "(i32, i64, Fn(i64) -> i64)",
        "(1, 40, f)",
        "            let (a, b, g) = t;
            return 0 - (a.as_i64() * 100 + b);",
    );
    let array = program(
        "([i32; 2], Fn(i64) -> i64)",
        "([1, 2], f)",
        "            let (arr, g) = t;
            return 0 - (arr[0].as_i64() * 10 + arr[1].as_i64());",
    );
    let none = program(
        "Option<Fn(i64) -> i64>",
        "None",
        "            return 0 - k;",
    );
    assert_eq!(neg(&tuple), 140);
    assert_eq!(neg(&array), 12);
    assert_eq!(neg(&none), 7);
}

/// An out-of-range literal in a generic part is reported once. The part is narrowed where it is
/// inferred (a pin) and again where it is fitted to the instance, and the second narrowing reported
/// it again: `g(x, 0 - 5000000000)` with `x: i32` was T071 twice (once on main), and an earlier
/// step of this change did the same for an annotated record field and enum payload (main ran the
/// payload). So did a tuple's element narrowed again at its generic argument or its `let` (T071
/// T071, T071 T041; main compiled both). Each narrowing now reports only at a span with no error
/// yet (`report_once`).
#[test]
fn out_of_range_literal_in_a_generic_part_is_reported_once() {
    let call = "module tool;
fn g<T>(a: T, b: T) -> i64 { return 1; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 1;
    return 0 - g(x, 0 - LIT);
}
";
    let field = "module tool;
record Hold<T> { v: T }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let h: Hold<i32> = Hold { v: 0 - LIT };
    return 0 - 1;
}
";
    let payload = "module tool;
enum G<T> { V(T), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e: G<i32> = G::V(0 - LIT);
    return 0 - 1;
}
";
    let tuple_argument = "module tool;
fn g<T>(a: T, t: (T, i64)) -> i64 { return 1; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 1;
    return 0 - g(x, (0 - LIT, 7));
}
";
    let tuple_let = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let t: (i32, i64) = (0 - LIT, 7);
    return 0 - 1;
}
";
    for template in [call, field, payload, tuple_argument, tuple_let] {
        let src = template.replace("LIT", "5000000000");
        assert_eq!(codes_of(&src), vec!["T071"], "{src}");
        assert_eq!(neg(&template.replace("LIT", "5")), 1);
    }
}

/// An out-of-range literal is reported though its value is typed `Type::Error` with no diagnostic.
/// `Either::L(7)` leaves `B` unbound, so `r` in the `Either::R(r)` arm has that type, and
/// `let y: i32 = r + 5000000000;` was T041 on main. An earlier step of this change skipped every
/// value typed `Type::Error` when it narrowed, to report a rejected one once, so the literal went
/// unreported and the backend panicked on the operand it could not lower. `b + 5000000000` with
/// `b: bool` lost its T041 the same way. Both keep main's codes.
#[test]
fn out_of_range_literal_beside_an_unreported_error_is_reported() {
    let either = "module tool;
enum Either<A, B> { L(A), R(B), N }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e = Either::L(7);
    match e {
        Either::L(a) => { return 0 - a; },
        Either::R(r) => {
            let y: i32 = r + 5000000000;
            return 0 - y.as_i64();
        },
        Either::N => { return 0; },
    }
    return 0;
}
";
    let bool_operand = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let b: bool = true;
    let x: i32 = b + 5000000000;
    return 0 - 1;
}
";
    assert_eq!(codes_of(either), vec!["T041"]);
    assert_eq!(codes_of(bool_operand), vec!["T054", "T041"]);
}

/// A slot whose type parameter a literal bound is compared as the instance is built, at the `i64`
/// default, through every type: `count(0, arr)` for `xs: &[T]` with `arr: [i32; 3]` passed the
/// literal's `&[i64]` slot (the fallback compared it with the literal still in it), and the
/// instance read the array's first element as the slice's length (7). The borrowed array binds
/// `T` to `i32` and reads back its length.
#[test]
fn slot_bound_by_a_literal_is_compared_at_the_default() {
    let template = "module tool;
fn count<T>(d: T, xs: &[T]) -> i64 {
    let n: u32 = xs.len();
    return n.as_i64();
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let arr: [i32; 3] = [7, 8, 9];
    return 0 - count(0, ARR);
}
";
    assert_eq!(codes_of(&template.replace("ARR", "arr")), vec!["T071"]);
    assert_eq!(neg(&template.replace("ARR", "&arr")), 3);
}

/// A function value whose return type a literal bound returns the `i64` its instance built, so it
/// does not pass for an `i32` return: `apply0(d, g)` with `d: i32` and `g` from `constf(7, c)`
/// trapped at the indirect call. It is T071; with `d: i64` it reads back.
#[test]
fn function_value_with_a_literal_typed_return_is_checked() {
    let template = "module tool;
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
fn apply0<T>(d: T, f: Fn() -> T) -> T { return f(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    let d: TYPE = 1;
    let r: TYPE = apply0(d, g);
    return 0 - r.as_i64();
}
";
    assert_eq!(codes_of(&template.replace("TYPE", "i32")), vec!["T071"]);
    assert_eq!(neg(&template.replace("TYPE", "i64")), 5);
}

/// A part of a function type that a literal typed reads alike at `u64`, which holds the bits of
/// the `i64` the function's instance computes, as a `u64` where a literal bound the parameter
/// does (X-M7). An earlier step of this change compared such a part at its `i64` default with
/// `type_compatible`, which rejects a `u64`, so three programs main ran correctly were T071, and
/// each reads 5 again: `apply0(d, g)` with `d: u64` and `g` from `constf(7, c)`, the same `g`
/// stored in a generic record's `Fn() -> T` field, and a `u64` closure stored in
/// `record H<T> { d: T, f: Fn(T) -> i64 }` beside a literal that bound `T`. An `i32` closure there
/// is still T071: the instance passes it an `i64`.
#[test]
fn literal_typed_part_of_a_function_reads_alike_at_u64() {
    let apply = "module tool;
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
fn apply0<T>(d: T, f: Fn() -> T) -> T { return f(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    let d: u64 = 1;
    let r: u64 = apply0(d, g);
    return 0 - r.as_i64();
}
";
    let field = "module tool;
record H<T> { d: T, f: Fn() -> T }
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    let d: u64 = 1;
    let h = H { d: d, f: g };
    let k = h.f;
    let r: u64 = k();
    return 0 - r.as_i64();
}
";
    let parameter = "module tool;
record H<T> { d: T, f: Fn(T) -> i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(v: TYPE) -> i64 { return v.as_i64(); };
    let h = H { d: 5, f: c };
    let k = h.f;
    return 0 - k(h.d);
}
";
    assert_eq!(neg(apply), 5);
    assert_eq!(neg(field), 5);
    assert_eq!(neg(&parameter.replace("TYPE", "u64")), 5);
    assert_eq!(codes_of(&parameter.replace("TYPE", "i32")), vec!["T071"]);
}

/// A function value whose return a literal typed is the `i64` its instance built, so it is a value
/// typed by a literal it is not wherever a slot narrows it, as a local bound by `let n = 5;` is.
/// Passed to a resolved call's `Fn() -> i32` parameter, bound by `let k: Fn() -> i32 = g;` or
/// returned as an `Fn() -> i32`, it was read as an `i32` and trapped at the indirect call, on main
/// too. It is now rejected with the site's own code (T071, T041, T049), and so is one whose
/// parameter a literal typed (`mkp(7, c)` bound as an `Fn(i32) -> i64`). A binding that is never
/// called is rejected too, where main ran it: the rule is per value, failing closed. At `i64` and
/// `u64`, which read its bits alike, each reads back 5.
#[test]
fn function_value_typed_by_a_literal_is_rejected_at_a_narrow_slot() {
    let call = "module tool;
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
fn apply(f: Fn() -> TYPE) -> TYPE { return f(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    let r: TYPE = apply(g);
    return 0 - r.as_i64();
}
";
    let binding = "module tool;
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    let k: Fn() -> TYPE = g;
    let r: TYPE = k();
    return 0 - r.as_i64();
}
";
    let returned = "module tool;
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
fn mk() -> Fn() -> TYPE {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    return g;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let k = mk();
    let r: TYPE = k();
    return 0 - r.as_i64();
}
";
    let parameter = "module tool;
fn mkp<T>(x: T, f: Fn(i64) -> i64) -> Fn(T) -> i64 { return f; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn(a: i64) -> i64 { return a + 1; };
    let k: Fn(TYPE) -> i64 = mkp(7, c);
    let y: TYPE = 4;
    return 0 - k(y);
}
";
    let never_called = "module tool;
fn constf<T>(x: T, f: Fn() -> i64) -> Fn() -> T { return f; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let c = fn() -> i64 { return 5; };
    let g = constf(7, c);
    let k: Fn() -> TYPE = g;
    return 0 - 5;
}
";
    for (template, code) in [
        (call, "T071"),
        (binding, "T041"),
        (returned, "T049"),
        (parameter, "T041"),
        (never_called, "T041"),
    ] {
        assert_eq!(codes_of(&template.replace("TYPE", "i32")), vec![code]);
        assert_eq!(neg(&template.replace("TYPE", "i64")), 5);
        assert_eq!(neg(&template.replace("TYPE", "u64")), 5);
    }
}

// ── a value typed by a literal it is not ────────────────────────────────────

/// A local bound by `let n = 7;` has an integer literal's type, but its value lowers at the `i64`
/// default, so narrowing it to an `i32` payload would store 8 bytes into the 4-byte slot (a
/// module that does not validate). It is rejected, naming the fix; the annotated twin reads back.
#[test]
fn literal_typed_local_in_a_narrow_payload_is_rejected() {
    let template = "module tool;
enum E { V(i32, i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b) => { return a.as_i64() * 100 + b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 7;
    return 0 - get(E::V(n, 40));
}
";
    assert_eq!(codes_of(&template.replace("BINDING", "")), vec!["T071"]);
    assert_eq!(neg(&template.replace("BINDING", ": i32")), 740);
}

/// The tuple form of the same mistake returned a wrong value rather than an invalid module: the
/// element was laid out at 8 bytes while `let (a, b) = t` read the slot's widths.
#[test]
fn literal_typed_local_in_a_narrow_tuple_element_is_rejected() {
    let template = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    let t: (i32, i64) = (n, 40);
    let (a, b) = t;
    return 0 - (a.as_i64() * 100 + b);
}
";
    assert_eq!(codes_of(&template.replace("BINDING", "")), vec!["T071"]);
    assert_eq!(neg(&template.replace("BINDING", ": i32")), 540);
}

/// A record field's value is a part of the construct too: it was laid out at 8 bytes in the
/// 4-byte field, so `s.b` read `40 << 32` beside it.
#[test]
fn literal_typed_local_in_a_narrow_record_field_is_rejected() {
    let template = "module tool;
record S { a: i32, b: i64 }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    let s: S = S { a: n, b: 40 };
    return 0 - (s.a.as_i64() * 100 + s.b);
}
";
    assert_eq!(codes_of(&template.replace("BINDING", "")), vec!["T071"]);
    assert_eq!(neg(&template.replace("BINDING", ": i32")), 540);
}

/// A call whose type is an integer literal's (`id(5)` binds `T` to the literal) is rejected the
/// same way; an `i64` payload has the value's own width and takes it unchanged.
#[test]
fn literal_typed_call_in_a_narrow_payload_is_rejected() {
    let template = "module tool;
enum E { V(SLOT, i64), N }
fn id<T>(x: T) -> T { return x; }
fn get(e: E) -> i64 {
    match e {
        E::V(a, b) => { return a.as_i64() * 100 + b; },
        E::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - get(E::V(id(5), 40));
}
";
    assert_eq!(codes_of(&template.replace("SLOT", "i32")), vec!["T071"]);
    assert_eq!(neg(&template.replace("SLOT", "i64")), 540);
}

/// Each `(template, codes, annotation, value)`: the template with `BINDING` removed must give
/// exactly `codes`, and with `BINDING` replaced by `annotation` must compile and return `value`.
fn assert_rejected_beside_annotated_twin(cases: &[(&str, &[&str], &str, i64)]) {
    for (template, codes, annotation, value) in cases {
        let untyped = template.replace("BINDING", "");
        assert_eq!(codes_of(&untyped), codes.to_vec(), "{untyped}");
        let typed = template.replace("BINDING", annotation);
        assert_eq!(neg(&typed), *value, "{typed}");
    }
}

/// A local bound by `let n = 5;` narrowed to a 4-byte slot outside a construct, too: at a call
/// argument, an annotated `let`, a return, an array element, or beside an `i32` operand. Each was
/// retyped while its value stayed 8 bytes, so the module compiled and the engine refused it, with
/// no diagnostic naming the cause. Each is now the site's own code (T071 for an argument, T041 for
/// a `let`, T049 for a return, T054 or T055 for an operand); the annotated twin reads back.
#[test]
fn literal_typed_binding_is_rejected_wherever_it_is_narrowed() {
    assert_rejected_beside_annotated_twin(&[
        (
            "module tool;
fn f(x: i32) -> i64 { return x.as_i64(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    return 0 - f(n);
}
",
            &["T071"],
            ": i32",
            5,
        ),
        (
            "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    let m: i32 = n;
    return 0 - m.as_i64();
}
",
            &["T041"],
            ": i32",
            5,
        ),
        (
            "module tool;
fn r() -> i32 {
    let n BINDING = 5;
    return n;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - r().as_i64();
}
",
            &["T049"],
            ": i32",
            5,
        ),
        (
            "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    let a: [i32; 2] = [n, 1];
    return 0 - (a[0].as_i64() * 10 + a[1].as_i64());
}
",
            &["T041"],
            ": i32",
            51,
        ),
        (
            "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    let x: i32 = 3;
    let s: i32 = x + n;
    return 0 - s.as_i64();
}
",
            &["T054"],
            ": i32",
            8,
        ),
        (
            "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let n BINDING = 5;
    let x: i32 = 5;
    if x == n {
        return 0 - 1;
    }
    return 0 - 2;
}
",
            &["T055"],
            ": i32",
            1,
        ),
    ]);
}

/// The compound form gave wrong values rather than refused modules: `let p = (5, 6);` binds
/// `(i64, i64)` storage under a literal tuple type, which every narrow tuple slot accepted, so its
/// readers took `(5, 0)` at the slot's offsets (and a narrow array, `[1, 0]`; a generic enum, its
/// `i64` instance). Before the fix each compiled: 500 at an argument, a `let`, a return, an
/// assignment and a record field, 5040 in a payload and in a tuple element, 10 for the array and
/// 171798692140 for the enum. Each is now the site's own code; the annotated twin reads back. The
/// rule is per value, not per read: an `Option` local whose only narrow part is its last one read
/// back right (5) by the little-endian layout, and is rejected too, failing closed.
#[test]
fn literal_typed_compound_binding_is_rejected_wherever_it_is_narrowed() {
    let pair =
        "fn f(t: (i32, i32)) -> i64 { let (a, b) = t; return a.as_i64() * 100 + b.as_i64(); }\n";
    let main = |prelude: &str, body: &str| {
        format!(
            "module tool;\n{prelude}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    let p BINDING = (5, 6);\n{body}\n}}\n"
        )
    };
    let read = "    let (a, b) = q;\n    return 0 - (a.as_i64() * 100 + b.as_i64());";
    let argument = main(pair, "    return 0 - f(p);");
    let let_annotation = main("", &format!("    let q: (i32, i32) = p;\n{read}"));
    let assignment = main(
        "",
        &format!("    let mut q: (i32, i32) = (0, 0);\n    q = p;\n{read}"),
    );
    let record_field = main(
        "record R { t: (i32, i32) }\n",
        &format!("    let r = R {{ t: p }};\n    let q = r.t;\n{read}"),
    );
    let payload = main(
        "enum E { V((i32, i32), i64), N }
fn get(e: E) -> i64 {
    match e {
        E::V(q, r) => { let (a, b) = q; return a.as_i64() * 1000 + b.as_i64() * 100 + r; },
        E::N => { return 0; },
    }
    return 0;
}
",
        "    return 0 - get(E::V(p, 40));",
    );
    let tuple_element = main(
        "",
        "    let t: ((i32, i32), i64) = (p, 40);
    let (q, r) = t;
    let (a, b) = q;
    return 0 - (a.as_i64() * 1000 + b.as_i64() * 100 + r);",
    );
    let ret = "module tool;
fn mk() -> (i32, i32) {
    let p BINDING = (5, 6);
    return p;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let (a, b) = mk();
    return 0 - (a.as_i64() * 100 + b.as_i64());
}
";
    let array = "module tool;
fn f(arr: [i32; 2]) -> i64 { return arr[0].as_i64() * 10 + arr[1].as_i64(); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let a BINDING = [1, 2];
    return 0 - f(a);
}
";
    let generic_enum = "module tool;
enum G<T> { V(T, i64), N }
fn get(e: G<i32>) -> i64 {
    match e {
        G::V(x, y) => { return x.as_i64() * 100 + y; },
        G::N => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let e BINDING = G::V(3, 40);
    return 0 - get(e);
}
";
    let option = "module tool;
fn f(o: Option<i32>) -> i64 {
    match o {
        Some(v) => { return v.as_i64(); },
        None => { return 0; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let o BINDING = Some(5);
    return 0 - f(o);
}
";
    assert_rejected_beside_annotated_twin(&[
        (&argument, &["T071"], ": (i32, i32)", 506),
        (&let_annotation, &["T041"], ": (i32, i32)", 506),
        (ret, &["T049"], ": (i32, i32)", 506),
        (&assignment, &["T045"], ": (i32, i32)", 506),
        (&record_field, &["T071"], ": (i32, i32)", 506),
        (&payload, &["T071"], ": (i32, i32)", 5640),
        (&tuple_element, &["T071"], ": (i32, i32)", 5640),
        (array, &["T071"], ": [i32; 2]", 12),
        (generic_enum, &["T071"], ": G<i32>", 340),
        (option, &["T071"], ": Option<i32>", 5),
    ]);
}

/// A rejected value is reported once, though a second narrowing reaches it: a generic call's
/// post-inference pass, a `let` around a pinned tuple, a `let` around an operator. Each gave the
/// code twice (T071 T071, T071 T041, T054 T041).
#[test]
fn literal_typed_binding_is_reported_once() {
    let main = |prelude: &str, body: &str| {
        format!(
            "module tool;\n{prelude}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{\n    let n = 5;\n    let x: i32 = 1;\n{body}\n}}\n"
        )
    };
    assert_eq!(
        codes_of(&main(
            "fn g<T>(a: T, b: T) -> i64 { return 0; }\n",
            "    return 0 - g(x, n + 1);"
        )),
        vec!["T071"]
    );
    assert_eq!(
        codes_of(&main(
            "",
            "    let t: (i32, i64) = (n + 1, 2);\n    return 0 - 1;"
        )),
        vec!["T071"]
    );
    assert_eq!(
        codes_of(&main(
            "",
            "    let s: i32 = x + (n + 1);\n    return 0 - 1;"
        )),
        vec!["T054"]
    );
}

// ── a bare variant several enums declare ────────────────────────────────────

/// A unit variant that several enums declare takes the enum its slot names, as a payload variant
/// does, and is T236 with no slot to choose. It used to take the first declaring enum in a
/// `HashMap`'s iteration order, so `let e: E2 = Q;` compiled or failed (T046) from run to run;
/// sixteen compiles make that chance 2^-16 here.
#[test]
fn ambiguous_bare_unit_variant_takes_the_slot_enum() {
    let src = |binding: &str| {
        format!(
            "module tool;
enum E1 {{ P, Q }}
enum E2 {{ Q, R }}
fn code(e: E2) -> i64 {{
    match e {{
        E2::Q => {{ return 1; }},
        E2::R => {{ return 2; }},
    }}
    return 0;
}}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let e{binding} = Q;
    return 0 - code(e);
}}
"
        )
    };
    for _ in 0..16 {
        assert_eq!(neg(&src(": E2")), 1);
    }
    assert_eq!(codes_of(&src("")), vec!["T236"]);
}

// ── CF-I1: a tuple slot that mentions a type parameter is not pinned ────────

/// A generic record field typed `(M<T>, i64)` used to count as concrete, so it was pinned as the
/// expected type of `mk(1)`, whose return-type inference then bound `U` to the outer `T` and the
/// compiler panicked in `mangle_type` ("ICE: unresolved generic `T`"). Now the slot is not pinned
/// and `U` is reported as uninferable. The second code is the instance body's own mismatch under
/// the unresolved `U`.
#[test]
fn tuple_slot_mentioning_a_type_parameter_is_not_pinned() {
    let src = "module tool;
enum M<T> { Jj(T), Nn }
record R<T> { t: (M<T>, i64) }
fn mk<U>(n: i64) -> (M<U>, i64) { return (Nn, n); }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let r = R { t: mk(1) };
    return 0 - 1;
}
";
    assert_eq!(codes_of(src), vec!["T150", "T049"]);
}

// ── known gaps (tests/attack/KNOWN_GAPS.md) ─────────────────────────────────

/// OPEN: an unannotated array literal takes its first element's type, and the homogeneity check
/// lets a later element built at other widths through (`(1, 10)` beside `(x, 20)` with
/// `x: i32`). The array reads every element as `(i64, i64)`, so `a[1]` reads wrong bytes.
#[test]
fn known_gap_mixed_width_array_elements() {
    let src = "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 7;
    let a = [(1, 10), (x, 20)];
    let (p, q) = a[1];
    return 0 - (p.as_i64() * 100 + q);
}
";
    assert_eq!(
        neg(src),
        8589934592700,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
}

/// OPEN, found while testing this fix and not part of it: a `match` on a `Result` built with the
/// `Ok(..)` / `Err(..)` shortcut runs the other arm. The shortcut lowers to `{ is_ok, value }` with
/// `is_ok = 1` for `Ok`, which `?` reads that way, while the match reads offset 0 as the stdlib
/// enum's variant index, where `Ok` is 0.
#[test]
fn known_gap_result_shortcut_match_runs_the_other_arm() {
    let template = "module tool;
fn get(r: Result<i32, i64>) -> i64 {
    match r {
        Ok(v) => { return 100 + v.as_i64(); },
        Err(e) => { return 200 + e; },
    }
    return 0;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let r: Result<i32, i64> = CTOR;
    return 0 - get(r);
}
";
    assert_eq!(
        neg(&template.replace("CTOR", "Ok(3)")),
        203,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
    assert_eq!(
        neg(&template.replace("CTOR", "Err(4)")),
        104,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
}

/// OPEN, found in this change's fifth review and not part of it: a `u64` passed where a literal
/// bound the type parameter is read by the literal's `i64` instance (X-M7), which computes on it
/// signed. `max(0, n)` with `n` at `u64::MAX` returns 0, since `0 > -1` signed; main does the
/// same. It closes with the inference change that takes the instance from the `u64`.
#[test]
fn known_gap_u64_where_a_literal_bound_the_instance_computes_signed() {
    let src = "module tool;
fn max<T>(a: T, b: T) -> T { if a > b { return a; } return b; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let m: i64 = 0 - 1;
    let n: u64 = m.as_u64();
    let r: u64 = max(0, n);
    if r == n {
        return 0 - 1;
    }
    return 0 - 2;
}
";
    assert_eq!(
        neg(src),
        2,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
}

/// OPEN, found in this change's fifth review and not part of it: a closure that reaches a generic
/// function or construct through anything but a top-level function-typed parameter keeps no effect
/// row. Its row is checked only against a formal written `Fn(..)` at the top level
/// (`bind_and_check_effect_rows`), so in the outer ring, which checks effects (a direct call to
/// `logs()` from the pure `tool_main` is E001), a closure performing `Log` passed as `b: T` beside a
/// pure one, inside a tuple, or stored in a generic record's `Fn(i64) -> T` field, is called from
/// the pure `tool_main`, which returns 9. The top-level twin is E001.
#[test]
fn known_gap_closure_effect_row_through_a_generic_parameter() {
    let header = "#[ring(outer)]
module tool;
effect Log;
fn logs() -> i64 ! { Log } { return 9; }
";
    let through_t = format!(
        "{header}fn pick<T>(a: T, b: T) -> T {{ return b; }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let p = fn(x: i64) -> i64 {{ return x; }};
    let q = fn(x: i64) -> i64 {{ return logs(); }};
    let g = pick(p, q);
    return 0 - g(1);
}}
"
    );
    let nested = format!(
        "{header}fn apply<T>(p: (Fn(i64) -> T, i64)) -> T {{
    let (f, k) = p;
    return f(k);
}}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let q = fn(x: i64) -> i64 {{ return logs(); }};
    return 0 - apply((q, 1));
}}
"
    );
    let field = format!(
        "{header}record H<T> {{ f: Fn(i64) -> T }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let q = fn(x: i64) -> i64 {{ return logs(); }};
    let h = H {{ f: q }};
    let g = h.f;
    return 0 - g(1);
}}
"
    );
    let top_level = format!(
        "{header}fn h<T>(f: Fn(i64) -> T, x: i64) -> T {{ return f(x); }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let q = fn(x: i64) -> i64 {{ return logs(); }};
    return 0 - h(q, 1);
}}
"
    );
    let direct = format!(
        "{header}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    return 0 - logs();
}}
"
    );
    assert_eq!(codes_of(&direct), vec!["E001"]);
    assert_eq!(codes_of(&top_level), vec!["E001"]);
    for src in [&through_t, &nested, &field] {
        assert_eq!(
            neg(src),
            9,
            "known gap moved: update tests/attack/KNOWN_GAPS.md"
        );
    }
}

/// OPEN, found in this change's eighth review and not part of it: a linear closure, one that
/// captures a typestate value, is checked for linearity at a resolved call's function-typed
/// parameter (T071) and at a generic enum's concrete function-typed payload (T071), but not
/// through a generic slot. A generic function's `Fn() -> i64` parameter, a generic enum's
/// `Fn() -> T` payload and a generic record's `Fn() -> T` field each take it, and the program calls
/// it twice: `shut` consumes the same `File<Open>` twice, and each returns 6 (3 + 3), as on main.
/// The two twins' T071 is the linearity check's: a closure that captures an `i64` instead passes
/// both and returns 6.
#[test]
fn known_gap_linear_closure_through_a_generic_slot_is_called_twice() {
    let header = "module tool;
state File { Open, Closed }
record File<@S> { fd: i64 }
fn open() -> File<Open> { return File { fd: 1 }; }
fn shut(f: File<Open>) -> File<Closed> { return File { fd: 0 }; }
";
    let linear = "    let a: File<Open> = open();
    let q = fn() -> i64 { let r: File<Closed> = shut(a); return r.fd + 3; };
";
    let generic_function = format!(
        "{header}fn twice<T>(d: T, f: Fn() -> i64) -> i64 {{ return f() + f(); }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{
{linear}    return 0 - twice(1, q);
}}
"
    );
    let generic_payload = format!(
        "{header}enum W<T> {{ F(Fn() -> T, T), N }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{
{linear}    let w = W::F(q, 7);
    match w {{
        W::F(g, k) => {{ return 0 - (g() + g()); }},
        W::N => {{ return 0; }},
    }}
    return 0;
}}
"
    );
    let generic_field = format!(
        "{header}record H<T> {{ d: T, f: Fn() -> T }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{
{linear}    let h = H {{ d: 1, f: q }};
    let g = h.f;
    return 0 - (g() + g());
}}
"
    );
    let resolved = format!(
        "{header}fn twice(f: Fn() -> i64) -> i64 {{ return f() + f(); }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{
{linear}    return 0 - twice(q);
}}
"
    );
    let concrete_payload = format!(
        "{header}enum W<T> {{ F(Fn() -> i64, T), N }}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{
{linear}    let w = W::F(q, 7);
    match w {{
        W::F(g, k) => {{ return 0 - (g() + g()); }},
        W::N => {{ return 0; }},
    }}
    return 0;
}}
"
    );
    assert_eq!(codes_of(&resolved), vec!["T071"]);
    assert_eq!(codes_of(&concrete_payload), vec!["T071"]);
    let plain = "    let a: i64 = 0;
    let q = fn() -> i64 { return a + 3; };
";
    assert_eq!(neg(&resolved.replace(linear, plain)), 6);
    assert_eq!(neg(&concrete_payload.replace(linear, plain)), 6);
    for src in [&generic_function, &generic_payload, &generic_field] {
        assert_eq!(
            neg(src),
            6,
            "known gap moved: update tests/attack/KNOWN_GAPS.md"
        );
    }
}

/// OPEN, found in this change's sixth review and not part of it: a method's argument is not checked
/// against its parameter's type, and a generic function's or generic impl's signature is not held
/// to the arity rule (T231). A `(i64, i64)` passed for a method's `(i32, i64)` parameter is read at
/// the parameter's offsets (171798691940; the free-function twin is T071). Either gap gives a value
/// that carries a payload an enum type written without type arguments, which a generic call
/// accepts in any instance's place: an `Option<i32>` passed to a generic impl's `o: Option`, or to
/// `x: T` of a `Holder<Option>` built from `Holder { v: None }`, reaches `or_default(o, 7)`, which
/// reads the 4-byte payload as 8 bytes (4294967301). `fn keep<T>(o: Option, d: T)` compiles, where
/// its non-generic twin is T231.
#[test]
fn known_gap_method_argument_is_not_checked() {
    let width = "module tool;
record Plain { k: i64 }
impl Plain {
    pub fn get(self: Plain, t: (i32, i64)) -> i64 {
        let (a, b) = t;
        return a.as_i64() * 100 + b;
    }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let p = Plain { k: 0 };
    let q: (i64, i64) = (1, 40);
    return 0 - p.get(q);
}
";
    let or_default = "fn or_default<T>(o: Option<T>, d: T) -> T {
    match o {
        Some(v) => { return v; },
        None => { return d; },
    }
    return d;
}
";
    let written = format!(
        "module tool;
record Holder<T> {{ v: T }}
impl Holder<T> {{
    pub fn peek(self: Holder<T>, o: Option) -> i64 {{ return or_default(o, 7); }}
}}
{or_default}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let x: i32 = 5;
    let s: Option<i32> = Some(x);
    let pad = fn(v: i64) -> i64 {{ return v; }};
    let h: Holder<i64> = Holder {{ v: 0 }};
    return 0 - (h.peek(s) + pad(0));
}}
"
    );
    let inferred = format!(
        "module tool;
record Holder<T> {{ v: T }}
impl Holder<T> {{
    pub fn put(self: Holder<T>, x: T) -> i64 {{ return or_default(x, 7); }}
}}
{or_default}pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
    let x: i32 = 5;
    let s: Option<i32> = Some(x);
    let pad = fn(v: i64) -> i64 {{ return v; }};
    let h = Holder {{ v: None }};
    return 0 - (h.put(s) + pad(0));
}}
"
    );
    let signature = "module tool;
fn keep<T>(o: Option, d: T) -> T { return d; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - keep(None, 5);
}
";
    let non_generic = "module tool;
fn keep(o: Option, d: i64) -> i64 { return d; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    return 0 - keep(None, 5);
}
";
    assert_eq!(codes_of(non_generic), vec!["T231"]);
    assert_eq!(
        neg(width),
        171798691940,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
    for src in [&written, &inferred] {
        assert_eq!(
            neg(src),
            4294967301,
            "known gap moved: update tests/attack/KNOWN_GAPS.md"
        );
    }
    assert_eq!(
        neg(signature),
        5,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
}

/// OPEN, found in this change's sixth review and not part of it: an unborrowed array passes for a
/// slice parameter. `type_compatible`'s slice arm, written for `&[T; N]`, also takes `[T; N]`, and
/// no coercion builds a slice at the call, so `count(arr)` for `xs: &[i32]` reads the array's first
/// element as its length (7). The borrowed twin reads back 3.
#[test]
fn known_gap_unborrowed_array_passes_for_a_slice_parameter() {
    let template = "module tool;
fn count(xs: &[i32]) -> i64 {
    let n: u32 = xs.len();
    return n.as_i64();
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let arr: [i32; 3] = [7, 8, 9];
    return 0 - count(ARR);
}
";
    assert_eq!(neg(&template.replace("ARR", "&arr")), 3);
    assert_eq!(
        neg(&template.replace("ARR", "arr")),
        7,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
}

/// OPEN, found in this change's sixth review and not part of it: `Option::None` with no slot is
/// typed `Option<Error>` without a diagnostic, and a later `Some(x)` with `x: i32` is assigned to
/// it. `Type::Error` is compatible with every type, so the fit of `pick(d, o)` for
/// `pick<T>(d: T, o: Option<T>)` with `d: i64` passes `Option<Error>` for the `Option<i64>` slot,
/// and the instance reads the 4-byte payload as 8 bytes (4294967301). The entry's other source, a
/// type parameter no payload binds, crashes the backend, so no test program pins it: the SHP gate
/// holds production's crashes to a shrink-only set.
#[test]
fn known_gap_unreported_error_type_argument_carries_a_payload() {
    let src = "module tool;
fn pick<T>(d: T, o: Option<T>) -> T {
    match o {
        Some(v) => { return v; },
        None => { return d; },
    }
    return d;
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let x: i32 = 5;
    let mut o = Option::None;
    o = Some(x);
    let pad = fn(v: i64) -> i64 { return v; };
    let d: i64 = 7;
    return 0 - (pick(d, o) + pad(0));
}
";
    assert_eq!(
        neg(src),
        4294967301,
        "known gap moved: update tests/attack/KNOWN_GAPS.md"
    );
}
