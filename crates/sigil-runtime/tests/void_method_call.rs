//! Unit/void-returning calls invoked as a STATEMENT must emit valid wasm.
//!
//! Regression coverage for an AIR→wasm codegen bug in internal calls to a
//! unit-returning callee. A void method (or free fn) called for its side
//! effect — `r.bump();` — lowered to `AirStmt::Call { dst: Some(v), .. }`
//! where `v` is a Unit-typed local. But a Unit-returning wasm function has
//! an EMPTY result list (it pushes nothing), so the call-site's
//! `local.set v` popped an empty operand stack. wasmtime rejected the
//! module at compile/validation time with
//!   `type mismatch: expected i32 but nothing on stack`.
//!
//! The fix: AIR lowering emits `dst: None` for a unit-returning call (the
//! `Option<VarId>` destination was designed for exactly this — the three
//! wasm call arms already skip `local.set` when `dst` is `None`).
//!
//! `compile_tool` SUCCEEDS for the buggy program (it produces bytes); the
//! invalid wasm only surfaces when wasmtime validates them. And
//! `execute_ephemeral` wraps a wasmtime compile failure as
//! `ToolError::Trapped { message: "failed to compile: …" }`, so a plain
//! "did it trap?" check cannot tell a real trap from invalid wasm — every
//! case here distinguishes the two on that message prefix.
//!
//! Invariant: a unit-returning internal call is EITHER a clean diagnostic
//! OR compiles + runs, but NEVER a wasm-validation failure.

use sigil_compiler::{compile_named_module, compile_tool};
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    /// Type-check rejected it (a clean compile error). Carries the codes.
    Diagnostic(Vec<String>),
    /// The module validated + instantiated (it ran).
    ValidWasm,
    /// `Module::new` rejected the bytes — the bug. Carries the message.
    InvalidWasm(String),
}

fn outcome(src: &str) -> Outcome {
    let compiled = match compile_tool(src) {
        Ok(c) => c,
        Err(e) => {
            return Outcome::Diagnostic(
                e.diagnostics()
                    .iter()
                    .map(|d| d.code().as_str().to_string())
                    .collect(),
            );
        }
    };
    match execute_ephemeral(&compiled.wasm, b"", compiled.fuel_budget, &IoGrants::none()) {
        Ok(_) => Outcome::ValidWasm,
        // A `Module::new` failure surfaces as `Trapped` with wasmtime's
        // "failed to compile: wasm[..]" prefix — the invalid-wasm signature.
        // Any OTHER trap (incl. the `return 0 - n` sentinel) means the
        // module instantiated fine, i.e. it WAS valid wasm.
        Err(ToolError::Trapped { message }) if message.contains("failed to compile") => {
            Outcome::InvalidWasm(message)
        }
        Err(_) => Outcome::ValidWasm,
    }
}

/// Decode the negative-sentinel return convention (`return 0 - value;` →
/// the runtime reports `Trapped` with a POSITIVE `value`).
fn neg(src: &str) -> i64 {
    let result = compile_tool(src).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            assert!(
                !message.contains("failed to compile"),
                "expected a clean sentinel return, got INVALID WASM: {message}"
            );
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected a sentinel"),
    }
}

// ── The reported repro: a void METHOD called internally ───────────────────────

const VOID_METHOD: &str = r#"module tool;
record R { x: i64 }
impl R {
  pub fn new() -> R { return R { x: 0 }; }
  pub fn bump(self: R @Mut) { self.x = self.x + 1; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut r: R = R::new();
    r.bump();
    return 0 - r.x;
}
"#;

#[test]
fn void_method_call_emits_valid_wasm() {
    let got = outcome(VOID_METHOD);
    assert!(
        !matches!(got, Outcome::InvalidWasm(_)),
        "INVALID WASM for a void method called internally: {got:?}\n--- source ---\n{VOID_METHOD}"
    );
    assert_eq!(got, Outcome::ValidWasm);
}

#[test]
fn void_method_call_runs_and_mutates() {
    // `bump` bumps x from 0 to 1; tool returns `0 - 1` → sentinel 1.
    assert_eq!(neg(VOID_METHOD), 1, "r.bump() should set r.x to 1");
}

#[test]
fn repeated_void_method_calls_run() {
    let src = r#"module tool;
record R { x: i64 }
impl R {
  pub fn new() -> R { return R { x: 0 }; }
  pub fn bump(self: R @Mut) { self.x = self.x + 1; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut r: R = R::new();
    r.bump();
    r.bump();
    r.bump();
    return 0 - r.x;
}
"#;
    assert_eq!(outcome(src), Outcome::ValidWasm);
    assert_eq!(neg(src), 3, "three bumps should set r.x to 3");
}

// ── Why the bug was METHOD-only: free unit fns can't even be called ───────────

#[test]
fn free_unit_fn_call_is_clean_t073_not_invalid_wasm() {
    // A direct call to a unit-returning FREE function is rejected at
    // type-check with T073 ("function returning `()` used as a value") —
    // it never reaches AIR/codegen. That guard is exactly why the
    // unit-call codegen bug only ever surfaced via METHODS (which are
    // checked through a method path that permits side-effecting `()`
    // returns). This pins that a free unit-fn call stays a CLEAN diagnostic
    // rather than ever degrading to invalid wasm.
    let src = r#"module tool;
fn noop(n: i64) { let z: i64 = n + 1; }
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    noop(7);
    return 0 - 5;
}
"#;
    assert_eq!(outcome(src), Outcome::Diagnostic(vec!["T073".into()]));
}

// ── The CallIndirect sibling is currently UN-REACHABLE from source ────────────

#[test]
fn unit_returning_closure_is_unwritable_never_invalid_wasm() {
    // `lower_call_expr` shares `call_dst` with `lower_indirect_call_expr`,
    // so the same `dst: None`-for-unit fix is applied to the CallIndirect
    // (closure) arms. That arm is not reachable with a unit return from
    // surface syntax today: the unit type `()` is rejected by the parser
    // (see `parse_type_expr`, AG-4) and an `Fn(...)` type REQUIRES a
    // parseable return type — so a unit-returning closure cannot be
    // declared. The fix is kept uniform across all call-lowering sites so
    // the "a valueless call has no destination" invariant holds at the
    // boundary regardless of which call kind reaches it. Whatever the
    // front-end does with this program, it must be a CLEAN diagnostic, not
    // invalid wasm.
    let src = r#"module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let g: Fn(i64) -> () = fn(x: i64) -> () { let z: i64 = x + 1; };
    g(7);
    return 0 - 5;
}
"#;
    let got = outcome(src);
    assert!(
        matches!(got, Outcome::Diagnostic(_)),
        "a unit-returning closure is unwritable; expected a clean diagnostic, got {got:?}"
    );
    assert!(
        !matches!(got, Outcome::InvalidWasm(_)),
        "never invalid wasm: {got:?}"
    );
}

// ── The value-returning control: already valid, must stay valid ───────────────

#[test]
fn value_returning_method_still_valid() {
    // The user-reported control: a method that returns i64 was always
    // WASM_VALID. Guard against the fix accidentally suppressing a real
    // (non-unit) `local.set`.
    let src = r#"module tool;
record R { x: i64 }
impl R {
  pub fn new() -> R { return R { x: 0 }; }
  pub fn bump2(self: R @Mut) -> i64 { self.x = self.x + 1; return self.x; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut r: R = R::new();
    let u: i64 = r.bump2();
    return 0 - u;
}
"#;
    assert_eq!(outcome(src), Outcome::ValidWasm);
    assert_eq!(neg(src), 1, "bump2 returns the post-increment x = 1");
}

// ── The 4th call site: a unit-returning EXTERN called as a statement ───────────

#[test]
fn unit_extern_call_statement_is_clean_t073_not_invalid_wasm() {
    // The `ExternCall` AIR site shares the `call_dst` fix too — keeping the "a valueless
    // call has no destination" invariant uniform across ALL call-lowering sites. Like
    // the free-unit-fn and unit-closure cases, this site is UNREACHABLE from source: a
    // unit-returning extern called as a statement is rejected at type-check with T073
    // ("does not return a value") before it ever reaches codegen, so it can only ever be
    // a CLEAN diagnostic — never invalid wasm. (An Err from the compiler means no wasm
    // bytes were produced, so an invalid-wasm outcome is impossible here by construction.)
    let src = "module m;\n\
        extern \"C\" fn fe_sink(x: i64) ! { FFI, Unsafe };\n\
        pub fn use_it(x: i64) -> i64 { fe_sink(x); return x; }\n";
    match sigil_compiler::compile_named_module("m.sigil", src) {
        Ok(_) => panic!("a unit-returning extern call statement must be a T073 diagnostic"),
        Err(e) => {
            let codes: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_string())
                .collect();
            assert!(
                codes.iter().any(|c| c == "T073"),
                "expected T073 (unit call as a value/statement), got {codes:?}"
            );
        }
    }
}

// ── The cap-grant CallIndirect site (air.rs lower_grant_expr) ─────────────────

/// Compile an ACTOR PROJECT and validate its emitted wasm via `Module::new`
/// (validation only — actors run under `RuntimeHost`, not the forge, so we do
/// not execute). Post-M011 a tool project may not declare an actor, so an actor
/// init body — the home of the cap-grant `CallIndirect` under test — is only
/// reachable in an actor project. This is the legitimate vehicle: an `entry
/// actor Main` spawns `Worker`, forcing `Worker`'s init to be lowered + emitted;
/// `Module::new` then rejects any invalid wasm the lowering would produce.
/// Mirrors `outcome`'s Diagnostic / ValidWasm / InvalidWasm trichotomy.
fn actor_outcome(src: &str) -> Outcome {
    let compiled = match compile_named_module("m.sigil", src) {
        Ok(c) => c,
        Err(e) => {
            return Outcome::Diagnostic(
                e.diagnostics()
                    .iter()
                    .map(|d| d.code().as_str().to_string())
                    .collect(),
            );
        }
    };
    let engine = wasmtime::Engine::default();
    match wasmtime::Module::new(&engine, &compiled.wasm_inner) {
        Ok(_) => Outcome::ValidWasm,
        Err(e) => Outcome::InvalidWasm(e.to_string()),
    }
}

#[test]
fn unit_grant_body_in_actor_init_emits_valid_wasm() {
    // A `grant(&cap, fn(c: &Cap) { ... })` whose closure body returns unit lowers
    // through the THIRD edited site — the cap-grant `AirStmt::CallIndirect`. The
    // grant lives in `Worker`'s init (caps only exist in actor context); an
    // `entry actor Main` spawns `Worker`, so its init is lowered + emitted, and a
    // bad `local.set` here would make the whole module invalid wasm.
    let src = r#"module tool;
cap type Fuel { burn }
actor Worker {
  state { hits: i64 }
  init(f: Fuel) {
    grant(&f, fn(c: &Fuel) { let z: i64 = 1 + 1; });
  }
  on Ping() -> i64 { return 0; }
}
entry actor Main {
  state { f: Fuel }
  on Start() -> i64 {
    let _w = spawn::<Worker>(f);
    return 0;
  }
}
"#;
    let got = actor_outcome(src);
    assert!(
        !matches!(got, Outcome::InvalidWasm(_)),
        "INVALID WASM for a unit-returning grant body: {got:?}"
    );
    assert_eq!(got, Outcome::ValidWasm);
}

#[test]
fn i64_grant_body_does_not_overfire_call_dst() {
    // Over-fire guard for the same cap-grant CallIndirect arm: an i64-returning grant
    // body MUST keep its `local.set` (call_dst → Some), or the pushed i64 result would
    // be left on the stack → invalid wasm. Proves the fix keys strictly on a Unit dst.
    let src = r#"module tool;
cap type Fuel { burn }
actor Worker {
  state { x: i64 }
  init(f: Fuel) {
    let r: i64 = grant(&f, fn(c: &Fuel) -> i64 { return 42; });
  }
  on Ping() -> i64 { return 0; }
}
entry actor Main {
  state { f: Fuel }
  on Start() -> i64 {
    let _w = spawn::<Worker>(f);
    return 0;
  }
}
"#;
    assert_eq!(actor_outcome(src), Outcome::ValidWasm);
}

// ── Generic monomorphization × void method ────────────────────────────────────

#[test]
fn two_monomorphizations_of_one_void_method() {
    // `call_dst` keys on the dst local's AirType, which after `apply_subst(Unit)` stays
    // Unit. Two DISTINCT monomorphizations of one void method (Box<i64>::poke and
    // Box<bool>::poke) must each independently gate their `local.set` — a regression
    // that didn't consult call_dst per-monomorph would emit invalid wasm on one callee.
    let src = r#"module tool;
record Box<T> { v: T, hits: i64 }
impl Box<T> {
  pub fn make(seed: T) -> Box<T> { return Box { v: seed, hits: 0 }; }
  pub fn poke(self: Box<T> @Mut) { self.hits = self.hits + 10; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut bi: Box<i64> = Box::make(7);
    let mut bb: Box<bool> = Box::make(true);
    bi.poke();
    bb.poke();
    bb.poke();
    let total: i64 = bi.hits + bb.hits;
    return 0 - total;
}
"#;
    let got = outcome(src);
    assert!(
        !matches!(got, Outcome::InvalidWasm(_)),
        "INVALID WASM for a monomorphized void method: {got:?}"
    );
    assert_eq!(got, Outcome::ValidWasm);
    assert_eq!(
        neg(src),
        30,
        "Box<i64>::poke (+10) and two Box<bool>::poke (+20) = 30"
    );
}

// ── The let-binding & reassignment lowering entry points ──────────────────────

#[test]
fn void_method_result_bound_to_let_and_reassigned() {
    // Distinct from the statement-call path the earlier tests cover: binding a void
    // result (`let mut u = r.bump();` → lower_statements Let → lower_expr_into) and
    // reassigning it (`u = r.bump();` → assign → lower_expr_into) both reach call_dst.
    // The never-set Unit local is harmless; both bumps still fire (r.x = 2).
    let src = r#"module tool;
record R { x: i64 }
impl R {
  pub fn new() -> R { return R { x: 0 }; }
  pub fn bump(self: R @Mut) { self.x = self.x + 1; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut r: R = R::new();
    let mut u = r.bump();
    u = r.bump();
    return 0 - r.x;
}
"#;
    let got = outcome(src);
    assert!(
        !matches!(got, Outcome::InvalidWasm(_)),
        "INVALID WASM for a let-bound/reassigned void result: {got:?}"
    );
    assert_eq!(got, Outcome::ValidWasm);
    assert_eq!(
        neg(src),
        2,
        "both bumps must fire despite the discarded unit result"
    );
}

// ── A valueless call consumed in a VALUE position (Eq) ────────────────────────

#[test]
fn two_unit_results_compared_with_eq() {
    // `type_compatible(Unit, Unit)` is true, so two void calls can be Eq operands. Both
    // reach codegen with gated `local.set`; the never-set i32(0) Unit locals compare
    // equal. Proves a valueless call in a value position preserves its side effect AND
    // yields the well-defined default-0 read (both bumps fire → r.x=2; u == v → 7).
    let src = r#"module tool;
record R { x: i64 }
impl R {
  pub fn new() -> R { return R { x: 0 }; }
  pub fn bump(self: R @Mut) { self.x = self.x + 1; }
}
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {
    let mut r: R = R::new();
    let u = r.bump();
    let v = r.bump();
    if u == v { return 0 - 7; }
    return 0 - 99;
}
"#;
    let got = outcome(src);
    assert!(
        !matches!(got, Outcome::InvalidWasm(_)),
        "INVALID WASM for two unit results compared with Eq: {got:?}"
    );
    // Either a clean ValidWasm (the slip-through path) or a clean diagnostic — but
    // never invalid wasm. The probe observed ValidWasm with sentinel 7.
    if got == Outcome::ValidWasm {
        assert_eq!(
            neg(src),
            7,
            "both bumps fire and u == v (both default-0 units)"
        );
    } else {
        assert!(matches!(got, Outcome::Diagnostic(_)));
    }
}
