//! Integration tests for the native 256-bit integer primitive (`u256`/`i256`)
//! — PR-U0 (type plumbing + the `u256_from_i64` constructor).
//!
//! Representation decision P: a 256-bit value is 32 bytes and cannot fit a wasm
//! local, so `Type::U256`/`Type::I256` lower to `AirType::Ptr` — a 4-byte pointer
//! to a 32-byte cell (4× i64 little-endian limbs) in linear memory, reusing the
//! existing record/`BumpAlloc`/`StoreField` machinery (zero new backend codegen).
//!
//! PR-U0 scope: declare/pass/return a u256, store it in a record field, and
//! construct one from a small i64 via `u256_from_i64`. Arithmetic, comparisons,
//! and wide (>64-bit) literals are DEFERRED to U1/U2 and must fail-closed here.

use sigil_compiler::compile_named_module;

fn assert_compiles_clean(source: &str, label: &str) {
    let result = compile_named_module(format!("u256_{label}.sigil"), source);
    if let Err(err) = result {
        let codes: Vec<&str> = err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str())
            .collect();
        panic!("expected clean compile for {label}, got: {codes:?}");
    }
}

fn assert_rejected(source: &str, label: &str) -> Vec<String> {
    let err = compile_named_module(format!("u256_{label}.sigil"), source)
        .expect_err(&format!("expected {label} to be rejected"));
    err.diagnostics()
        .iter()
        .map(|d| d.code().as_str().to_owned())
        .collect()
}

#[test]
fn u256_param_passthrough() {
    // The pointer-backed 32-byte value crosses a function boundary as a pointer.
    let source = r#"
module main;

fn id(x: u256) -> u256 {
    return x;
}
"#;
    assert_compiles_clean(source, "passthrough");
}

#[test]
fn i256_param_passthrough() {
    // i256 shares the identical representation; plumbing must accept it too.
    let source = r#"
module main;

fn id(x: i256) -> i256 {
    return x;
}
"#;
    assert_compiles_clean(source, "i256_passthrough");
}

#[test]
fn u256_record_field_roundtrip() {
    // A u256 lives in a record field (a 4-byte pointer slot) and reads back.
    let source = r#"
module main;

record Account { balance: u256 }

fn get_balance(a: Account) -> u256 {
    return a.balance;
}
"#;
    assert_compiles_clean(source, "field_roundtrip");
}

#[test]
fn u256_from_i64_constructs() {
    // The minimal U0 constructor: a fresh 32-byte cell, limb0 = x, limbs 1-3 = 0.
    let source = r#"
module main;

fn make_zero() -> u256 {
    let z: u256 = u256_from_i64(0);
    return z;
}

fn make_one() -> u256 {
    return u256_from_i64(1);
}
"#;
    assert_compiles_clean(source, "from_i64");
}

#[test]
fn u256_construct_into_record_and_reassign() {
    // Construct directly into a record field, and reassign a `let mut` u256
    // local (rebinds the pointer to a fresh cell — the immutable-value
    // discipline keeps this sound).
    let source = r#"
module main;

record Account { balance: u256 }

fn boot() -> u256 {
    let mut b: u256 = u256_from_i64(1);
    b = u256_from_i64(2);
    let a: Account = Account { balance: b };
    return a.balance;
}
"#;
    assert_compiles_clean(source, "construct_reassign");
}

#[test]
fn u256_add_sub_and_comparisons_compile() {
    // PR-U1a: `+`/`-` and comparisons are backed by checked stdlib multi-limb
    // math (operator → Call rewrite). Value-correctness is covered by execution
    // tests in sigil-runtime (tests/u256_arithmetic.rs); here we gate that the
    // surface operators type-check + lower to valid wasm.
    let source = r#"
module main;

fn sum(a: u256, b: u256) -> u256 { return a + b; }
fn diff(a: u256, b: u256) -> u256 { return a - b; }
fn prod(a: u256, b: u256) -> u256 { return a * b; }
fn quot(a: u256, b: u256) -> u256 { return a / b; }
fn rem(a: u256, b: u256) -> u256 { return a % b; }
fn band(a: u256, b: u256) -> u256 { return a & b; }
fn bor(a: u256, b: u256) -> u256 { return a | b; }
fn shl(a: u256, b: u256) -> u256 { return a << b; }
fn shr(a: u256, b: u256) -> u256 { return a >> b; }
fn less(a: u256, b: u256) -> bool { return a < b; }
fn ge(a: u256, b: u256) -> bool { return a >= b; }
fn eq(a: u256, b: u256) -> bool { return a == b; }
fn ne(a: u256, b: u256) -> bool { return a != b; }
"#;
    assert_compiles_clean(source, "u1_ops");
}

#[test]
fn u256_aggregate_equality_is_fail_closed() {
    // Adversarial review F1 (E3/E6): `==`/`!=` on a tuple/record CONTAINING a
    // u256 would fall through to pointer-eq (wrong for value types) — must be
    // rejected, not silently mis-compiled.
    let tup = r#"
module main;
fn f(a: u256, b: u256) -> bool {
    let pa: (u256, u256) = (a, b);
    let pb: (u256, u256) = (a, b);
    return pa == pb;
}
"#;
    assert!(
        !assert_rejected(tup, "tuple_eq").is_empty(),
        "== on a tuple-of-u256 must be fail-closed (F1)"
    );
    let rec = r#"
module main;
record Pair { x: u256, y: i64 }
fn f(p: Pair, q: Pair) -> bool { return p != q; }
"#;
    assert!(
        !assert_rejected(rec, "record_eq").is_empty(),
        "!= on a record containing u256 must be fail-closed (F1)"
    );
}

#[test]
fn i256_comparison_is_fail_closed() {
    // Adversarial review F2 (E4): bare i256 `==` type-checked but lowered to
    // pointer-eq. i256 has no value-semantics yet → reject.
    let source = "module main;\nfn f(a: i256, b: i256) -> bool { return a == b; }\n";
    assert!(
        !assert_rejected(source, "i256_eq").is_empty(),
        "i256 == must be fail-closed (F2)"
    );
}

#[test]
fn user_module_u256_is_clean_error_not_ice() {
    // Adversarial review F4: a user `module u256;` using u256 arithmetic used to
    // suppress stdlib injection and then ICE at operator lowering. It must now be
    // a clean diagnostic (M002 duplicate module) — assert_rejected catches an
    // Err; a panic would crash this test, which is itself the regression signal.
    let source = r#"
module u256;
fn f() -> u256 {
    let a: u256 = u256_from_i64(1);
    let b: u256 = u256_from_i64(2);
    return a + b;
}
"#;
    let codes = assert_rejected(source, "user_mod_u256");
    assert!(
        codes.iter().any(|c| c == "M002"),
        "user `module u256;` + arithmetic must be a clean M002, got: {codes:?}"
    );
}

#[test]
fn wide_and_small_literals_compile() {
    // PR-U2: small (i64-fitting) and wide (>2^63, <2^256) decimal literals both
    // construct u256 cells and flow through arithmetic.
    let src = "module main;\nfn f() -> u256 { let a: u256 = 0; let b: u256 = 1000; \
        let c: u256 = 1000000000000000000000000; return a + b + c; }\n";
    assert_compiles_clean(src, "u2_literals");
}

#[test]
fn wide_literal_over_2pow256_is_rejected() {
    // 2^256 exactly — out of u256 range → L001 at lex time, never a wrapped value.
    let src = "module main;\nfn f() -> u256 { let x: u256 = \
        115792089237316195423570985008687907853269984665640564039457584007913129639936; \
        return x; }\n";
    let codes = assert_rejected(src, "over_2pow256");
    assert!(
        codes.iter().any(|c| c == "L001"),
        "a >= 2^256 literal must be L001, got: {codes:?}"
    );
}

#[test]
fn hex_literals_compile_and_overflow_rejected() {
    // PR-U2-b: a wide hex literal (an address/hash; here 2^256-1 = 64 f's) compiles
    // to a u256, while 2^256 (a 1 + 64 zeros) is rejected at lex time (L001).
    let ok = "module main;\nfn f() -> u256 { let m: u256 = \
        0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff; return m; }\n";
    assert_compiles_clean(ok, "hex_max");
    let over = "module main;\nfn f() -> u256 { let m: u256 = \
        0x10000000000000000000000000000000000000000000000000000000000000000; return m; }\n";
    let codes = assert_rejected(over, "hex_over");
    assert!(
        codes.iter().any(|c| c == "L001"),
        "a 2^256 hex literal must be L001, got: {codes:?}"
    );
}

#[test]
fn wide_literal_in_i64_context_is_rejected() {
    // A wide literal types as u256; assigning it to an i64 binding is a clean
    // type error (never a silent truncation).
    let src = "module main;\nfn f() -> i64 { let x: i64 = 18446744073709551616; return x; }\n";
    assert!(
        !assert_rejected(src, "wide_in_i64").is_empty(),
        "a wide literal in i64 context must be rejected"
    );
}

#[test]
fn i256_arithmetic_still_fail_closed() {
    // i256 has the type plumbing but no value-semantics yet (E4): all i256
    // arithmetic/bitwise/shift must be cleanly rejected, never mis-dispatched to
    // the unsigned u256 ops. (u256 itself now supports the full + - * / % & | << >>.)
    for op in ["+", "-", "*", "/", "%", "&", "|", "<<", ">>"] {
        let source =
            format!("module main;\nfn f(a: i256, b: i256) -> i256 {{ return a {op} b; }}\n");
        let codes = assert_rejected(&source, "no_i256_arith");
        assert!(
            !codes.is_empty(),
            "i256 `{op}` must be fail-closed (E4), got a clean compile"
        );
    }
}

#[test]
fn u256_from_i64_rejects_non_integer_operand() {
    // The constructor's operand must be a machine integer.
    let source = r#"
module main;

fn bad(s: str) -> u256 {
    return u256_from_i64(s);
}
"#;
    let codes = assert_rejected(source, "ctor_bad_arg");
    assert!(
        codes.iter().any(|c| c == "T075"),
        "expected T075 for non-integer u256_from_i64 operand, got: {codes:?}"
    );
}

#[test]
fn u256_not_sendable_across_actors_yet() {
    // E7 fail-closed: SENDING a u256 across an actor boundary is rejected until
    // 32-byte value-serialization lands (a raw pointer is not portable across
    // per-actor memories). The check fires at the send site (the actual
    // crossing), not the handler declaration — `is_send_type(u256) == false`.
    let source = r#"
module sigil;

cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }
    on Start(worker: ActorRef<Worker>) -> i64 {
        worker.send(Deposit(u256_from_i64(1)));
        return 0;
    }
}

actor Worker {
    init(fuel: Fuel) {}
    on Deposit(amount: u256) {}
}
"#;
    let codes = assert_rejected(source, "no_send");
    assert!(
        !codes.is_empty(),
        "sending a u256 across an actor boundary must be rejected (E7), got a clean compile"
    );
}
