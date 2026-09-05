//! Sound `trap()` divergence (Tier A). `trap()` is typed the bottom type `Never`;
//! the return checker treats a statement whose expression type is `Never` as
//! terminating its path (reading the TYPE, not the `trap()` syntax). So a
//! non-unit function may end in `trap();` without an explicit `return` after it,
//! and the block lowers to a terminating `unreachable`.
//!
//! Value-position `trap()` (used AS a value: `return trap()`, `let x = trap()`)
//! is Tier B — fail-closed here (no `Never <: T` rule), i.e. rejected, never
//! silently accepted.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    if let Err(err) = compile_named_module(format!("trap_div_{label}.sigil"), source) {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_fails(source: &str, label: &str) {
    assert!(
        compile_named_module(format!("trap_div_{label}.sigil"), source).is_err(),
        "expected compile failure for {label} (Tier-A fail-closed boundary), but it compiled"
    );
}

/// F003 regression: a value-position `trap()` in an INFERENCE position (no
/// expected type to reject it against) must be rejected at TYPE-CHECK with the
/// specific `code`, NEVER silently accepted and left to ICE at AIR's C-NEVER
/// backstop (`lower_type` / `mangle_type` `panic!`). If the fix is reverted these
/// cases panic inside `compile_named_module` — which still fails the test, but
/// asserting the exact code also pins the diagnostic contract.
fn assert_fails_with_code(source: &str, label: &str, code: &str) {
    match compile_named_module(format!("trap_div_{label}.sigil"), source) {
        Ok(_) => panic!("expected {code} for {label} (value-position `never`), but it compiled"),
        Err(err) => {
            let codes: Vec<&str> = err
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str())
                .collect();
            assert!(
                codes.contains(&code),
                "expected {code} for {label}, got: {codes:?}"
            );
        }
    }
}

#[test]
fn trap_terminates_after_partial_return() {
    // `if c { return } … trap()` — trap() as the terminating tail statement of a
    // non-unit fn. Was missing-return (T044) when trap() was Unit; now compiles.
    assert_compiles_clean(
        r#"
module main;
fn pick(c: bool, x: i64) -> i64 {
    if c {
        return x;
    }
    trap();
}
"#,
        "partial_return",
    );
}

#[test]
fn trap_as_sole_body_compiles() {
    // The block ends in a diverging `trap()` — lowers to a terminating
    // `unreachable`, valid for the `i64` return type (value never produced).
    assert_compiles_clean(
        r#"
module main;
fn always_abort() -> i64 {
    trap();
}
"#,
        "sole_body",
    );
}

#[test]
fn trap_in_both_if_arms_propagates_divergence() {
    // Both arms diverge → the `if` guarantees the path ends → no explicit return
    // needed after it.
    assert_compiles_clean(
        r#"
module main;
fn both(c: bool) -> i64 {
    if c {
        trap();
    } else {
        trap();
    }
}
"#,
        "both_arms",
    );
}

#[test]
fn trap_still_works_as_a_plain_guard_statement() {
    // The #442 usage shape: `trap();` in a guard, with a real `return` after.
    assert_compiles_clean(
        r#"
module main;
fn checked(i: i64) -> i64 {
    if i < 0 {
        trap();
    }
    return i;
}
"#,
        "guard",
    );
}

#[test]
fn return_trap_is_rejected_tier_a_boundary() {
    // Value-position: `return trap()` needs `Never <: i64` (Tier B). Rejected.
    assert_fails(
        r#"
module main;
fn bad() -> i64 {
    return trap();
}
"#,
        "return_trap",
    );
}

#[test]
fn let_bound_trap_as_value_is_rejected() {
    // `let x: i64 = trap()` needs `Never <: i64` (Tier B). Rejected.
    assert_fails(
        r#"
module main;
fn bad() -> i64 {
    let x: i64 = trap();
    return x;
}
"#,
        "let_trap",
    );
}

// ── F003: value-position `trap()` in INFERENCE positions (no expected type to
// reject against) — these SILENTLY reached AIR and ICE'd at the C-NEVER backstop
// before the T279 gate. Each must now fail type-check with T279. The annotated
// positions above (`return trap()`, `let x: i64 = trap()`) already failed via the
// clashing-target `type_compatible`; T279 closes the four inference holes. ──

#[test]
fn f003_bare_unannotated_let_trap_is_t279() {
    // `let x = trap()` — NO annotation, so the binding type infers to `never`
    // with nothing to reject it. Was `ICE: Type::Never reached lower_type`.
    assert_fails_with_code(
        r#"
module main;
fn f() -> i64 {
    let x = trap();
    return 0;
}
"#,
        "bare_let",
        "T279",
    );
}

#[test]
fn f003_tuple_element_trap_is_t279() {
    // `(trap(), 1)` — tuple elements infer independently with no expected type;
    // the `never` limb was mangled into the tuple key. Was `ICE: … mangle_type`.
    assert_fails_with_code(
        r#"
module main;
fn f() -> i64 {
    let t = (trap(), 1);
    return 0;
}
"#,
        "tuple_elem",
        "T279",
    );
}

#[test]
fn f003_tuple_element_trap_even_annotated_is_t279() {
    // A tuple annotation does not push per-element expected types before the
    // tuple is built, so `let t: (i64, i64) = (trap(), 1)` also ICE'd.
    assert_fails_with_code(
        r#"
module main;
fn f() -> i64 {
    let t: (i64, i64) = (trap(), 1);
    return 0;
}
"#,
        "tuple_elem_annotated",
        "T279",
    );
}

#[test]
fn f003_all_never_array_trap_is_t279() {
    // `[trap()]` — element 0 sets the inferred element type to `never` with no
    // second element to trigger the T140 homogeneity check. Was `ICE: lower_type`.
    assert_fails_with_code(
        r#"
module main;
fn f() -> i64 {
    let a = [trap()];
    return 0;
}
"#,
        "all_never_array",
        "T279",
    );
}

#[test]
fn f003_generic_call_arg_trap_is_t279() {
    // `id(trap())` — a generic parameter unifies with `never`, binding `T` to the
    // bottom type; the monomorphization key then ICE'd at `mangle_type`.
    assert_fails_with_code(
        r#"
module main;
fn id<T>(x: T) -> i64 {
    return 0;
}
fn f() -> i64 {
    return id(trap());
}
"#,
        "generic_call_arg",
        "T279",
    );
}

#[test]
fn f003_generic_record_field_trap_is_t279() {
    // `Box { val: trap() }` — a generic field's value binds `T = never` (the
    // record path skips the concrete T071 check for generic fields).
    assert_fails_with_code(
        r#"
module main;
record Box<T> { val: T }
fn f() -> i64 {
    let b = Box { val: trap() };
    return 0;
}
"#,
        "generic_record_field",
        "T279",
    );
}

#[test]
fn f003_generic_enum_payload_trap_is_t279() {
    // `Some(trap())` — the stdlib `Option<T>` payload binds `T = never`; the
    // generic-enum instantiation ICE'd at `mangle_type`.
    assert_fails_with_code(
        r#"
module main;
fn f() -> i64 {
    let o = Some(trap());
    return 0;
}
"#,
        "generic_enum_payload",
        "T279",
    );
}

#[test]
fn f003_user_enum_payload_trap_is_t279() {
    // `V(trap())` for a USER-declared enum. A bare-variant call routes through
    // `infer_call_expr` → `infer_arg_with_expected` — the same T279 choke as any
    // other call argument. The untyped `Expr::EnumConstruct` direct-construction
    // node (which once had its own field-inference loop that bypassed that choke)
    // is never emitted by the parser/frontends/desugar, so THIS call path is the
    // only way a `trap()` ever reaches an enum payload. A concrete `i64` payload:
    // the `never` value is poisoned to `Type::Error`, never mangled into AIR.
    assert_fails_with_code(
        r#"
module main;
enum E { V(i64), Empty }
fn f() -> i64 {
    let e = V(trap());
    return 0;
}
"#,
        "user_enum_payload",
        "T279",
    );
}

#[test]
fn f003_user_generic_enum_payload_trap_is_t279() {
    // The user-defined generic analogue of `Some(trap())`: `V`'s payload binds
    // `T = never`, so the monomorphization key would ICE at `mangle_type` without
    // the T279 gate. Covers a user enum in addition to the stdlib `Option<T>`.
    assert_fails_with_code(
        r#"
module main;
enum E<T> { V(T), Empty }
fn f() -> i64 {
    let e = V(trap());
    return 0;
}
"#,
        "user_generic_enum_payload",
        "T279",
    );
}

#[test]
fn f003_nested_tuple_trap_is_single_t279() {
    // `((trap(), 1), 2)` — the inner tuple is poisoned to a concrete placeholder
    // at construction, so the OUTER tuple sees no `never` and the error is
    // reported exactly once (no cascade, no ICE).
    match compile_named_module(
        "trap_div_nested_tuple.sigil".to_string(),
        r#"
module main;
fn f() -> i64 {
    let t = ((trap(), 1), 2);
    return 0;
}
"#,
    ) {
        Ok(_) => panic!("expected T279 for nested_tuple, but it compiled"),
        Err(err) => {
            let t279s = err
                .diagnostics()
                .iter()
                .filter(|d| d.code().as_str() == "T279")
                .count();
            assert_eq!(
                t279s, 1,
                "expected exactly one T279 (no cascade), got {t279s}"
            );
        }
    }
}

#[test]
fn f003_legal_trap_statement_forms_still_compile() {
    // The Tier-A divergence forms (bare `trap();`, guard, both-if-arms) must stay
    // clean — the T279 value-position gate must not touch STATEMENT-position trap.
    assert_compiles_clean(
        r#"
module main;
fn guard(i: i64) -> i64 {
    if i < 0 {
        trap();
    }
    return i;
}
fn sole() -> i64 {
    trap();
}
fn both(c: bool) -> i64 {
    if c {
        trap();
    } else {
        trap();
    }
}
fn ok_tuple() -> i64 {
    let t = (1, 2);
    return 0;
}
fn ok_array() -> i64 {
    let a = [1, 2, 3];
    return 0;
}
"#,
        "legal_forms_after_t279",
    );
}
