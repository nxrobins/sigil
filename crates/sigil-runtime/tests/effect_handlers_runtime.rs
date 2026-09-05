//! Effect Handlers (EH4) — runtime execution tests. The evidence-passing desugar
//! lowers a handler to ordinary closure-passing wasm; these compile + RUN it.
//!
//! Result convention (shared with the other runtime suites): the tool ends in
//! `return 0 - <value>;`, which traps as `tool returned error (<value>)`.

mod common;

const FUEL: u64 = 10_000_000;

fn run_returning_negative(source: &str) -> i64 {
    common::run_returning_negative_with_fuel(source, FUEL)
}

/// EH4.0: a scoped single-operation handler runs end-to-end. `f` performs
/// `Reader.get()`; the handler resumes 42; `f` returns it.
#[test]
fn eh40_scoped_resume_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle f() { Reader.get() => resume 42 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.0: an operation with a parameter — the clause binder is bound to the
/// performed argument and the resumed value is computed from it.
#[test]
fn eh40_scoped_resume_with_binder_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Calc { fn add1(x: i64) -> i64; }\n\
        fn f() -> i64 ! { Calc } { return perform Calc.add1(10); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle f() { Calc.add1(x) => resume x + 1 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 11);
}

/// EH4.0: the performer uses the resumed value in further computation (`base * 2`),
/// proving the resumed value flows back to the perform site and execution continues.
#[test]
fn eh40_resumed_value_flows_back_to_perform_site() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        fn f() -> i64 ! { Reader } { let base = perform Reader.get(); return base * 2; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle f() { Reader.get() => resume 21 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.1: a multi-operation effect (State: get + put). The performer performs BOTH
/// operations; the handler covers both with one clause each. Each operation gets its
/// own evidence closure, threaded in sorted-op order, and both resume correctly.
#[test]
fn eh41_multi_op_effect_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect State { fn get() -> i64; fn put(v: i64) -> i64; }\n\
        fn worker() -> i64 ! { State } { let a = perform State.get(); let b = perform State.put(a + 1); return a + b; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle worker() { State.get() => resume 10, State.put(x) => resume x * 2 }; return 0 - r; }\n";
    // get => 10 → a = 10; put(a+1) = put(11) => x*2 = 22 → b = 22; a + b = 32.
    assert_eq!(run_returning_negative(src), 32);
}

/// EH4.2: an ABORTIVE handler. `parse` performs `Fail.raise` (an `-> never` op) on
/// the error path; the abortive clause's value becomes the value of the whole handle,
/// abandoning the rest of `parse`. Here the error path is taken → 99.
#[test]
fn eh42_abortive_clause_aborts() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn parse(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x * 2; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle parse(0 - 5) { Fail.raise(m) => 99 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 99);
}

/// EH4.2: the SAME handler on the NON-error path — `parse` never performs `raise`, so
/// it returns its normal value (untouched), not the abortive clause's value.
#[test]
fn eh42_abortive_normal_path_returns_normally() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn parse(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x * 2; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle parse(21) { Fail.raise(m) => 99 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.2 × EH4.1: a MIXED effect — one scoped op (`get`) and one abortive op
/// (`fail`). On the abort path the abortive clause wins over the (already-resumed)
/// scoped value. worker(-3): get resumes 10, then fail aborts → 77.
#[test]
fn eh42_mixed_scoped_and_abortive_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Mixed { fn get() -> i64; fn fail() -> never; }\n\
        fn worker(x: i64) -> i64 ! { Mixed } { let base = perform Mixed.get(); if x < 0 { perform Mixed.fail(); } return base + x; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle worker(0 - 3) { Mixed.get() => resume 10, Mixed.fail() => 77 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 77);
}

/// EH4.2 × EH4.1: the same mixed handler, abort path NOT taken — scoped `get` resumes
/// 10, no `fail`, normal return. worker(3): 10 + 3 = 13.
#[test]
fn eh42_mixed_normal_path_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Mixed { fn get() -> i64; fn fail() -> never; }\n\
        fn worker(x: i64) -> i64 ! { Mixed } { let base = perform Mixed.get(); if x < 0 { perform Mixed.fail(); } return base + x; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle worker(3) { Mixed.get() => resume 10, Mixed.fail() => 77 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 13);
}

/// EH4.2 sweep D1 (abortive): a NARROW-int (`i32`) operation parameter with an
/// integer-LITERAL perform arg and the binder USED in the abortive clause. Before the
/// fix this compiled cleanly but emitted non-validating wasm (the literal stayed
/// `IntLit` → mangled i64 against the i32 closure binder). Now the literal is narrowed
/// to the declared `i32`, so it validates and runs: abort → c(=7) + 5 = 12.
#[test]
fn eh42_narrow_int_literal_arg_abortive_runs() {
    // Sentinel 1 ⟺ the i32 result was exactly 12 (abort → c(=7) + 5). A wrong/
    // truncated value yields 2; non-validating wasm would have trapped/failed.
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(c: i32) -> never; }\n\
        fn parse(x: i32) -> i32 ! { Fail } { if x < 0 { perform Fail.raise(7); } return x * 2; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r: i32 = handle parse(0 - 1) { Fail.raise(c) => c + 5 }; if r == 12 { return 0 - 1; } return 0 - 2; }\n";
    assert_eq!(run_returning_negative(src), 1);
}

/// EH4.2 sweep D1 (scoped/EH4.1): the same narrow-int-literal-arg + binder-using
/// clause on the SCOPED path (the bug lived in the shared evidence construction).
/// `get(7)` resumes `c + 5` = 12.
#[test]
fn eh41_narrow_int_literal_arg_scoped_runs() {
    // Sentinel 1 ⟺ the i32 result was exactly 12 (get(7) resumes c + 5).
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect R { fn get(c: i32) -> i32; }\n\
        fn parse() -> i32 ! { R } { return perform R.get(7); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r: i32 = handle parse() { R.get(c) => resume c + 5 }; if r == 12 { return 0 - 1; } return 0 - 2; }\n";
    assert_eq!(run_returning_negative(src), 1);
}

/// EH4.3a: SCOPED PROPAGATION — the handler wraps `g`, which does NOT perform
/// directly; it calls `helper`, which performs `Reader.get`. Evidence threads handle
/// → g → helper. helper resumes 41, g adds 1 → 42.
#[test]
fn eh43_scoped_propagation_one_level_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        fn helper() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        fn g() -> i64 ! { Reader } { let a = helper(); return a + 1; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { Reader.get() => resume 41 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.3a: propagation across THREE frames — `g` → `h` → `k`, only `k` performs.
/// Evidence forwards down the whole chain.
#[test]
fn eh43_scoped_propagation_three_levels_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        fn k() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        fn h() -> i64 ! { Reader } { return k(); }\n\
        fn g() -> i64 ! { Reader } { return h(); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { Reader.get() => resume 42 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.3a: multi-OP propagation — `g` calls two helpers, one performing `State.get`
/// and one `State.put`; each is a subset-performer that still receives evidence for
/// both ops (threaded from the effect declaration). get→10, put(11)→22, sum 32.
#[test]
fn eh43_multi_op_propagation_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect State { fn get() -> i64; fn put(v: i64) -> i64; }\n\
        fn reader() -> i64 ! { State } { return perform State.get(); }\n\
        fn writer(x: i64) -> i64 ! { State } { return perform State.put(x); }\n\
        fn g() -> i64 ! { State } { let a = reader(); let b = writer(a + 1); return a + b; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { State.get() => resume 10, State.put(x) => resume x * 2 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 32);
}

/// EH4.3a: a subset-performer (performs only `get`, handler covers `get` + `put`) now
/// compiles and runs — the unused `put` evidence is never called.
#[test]
fn eh43_subset_performer_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect State { fn get() -> i64; fn put(v: i64) -> i64; }\n\
        fn worker() -> i64 ! { State } { return perform State.get(); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle worker() { State.get() => resume 33, State.put(x) => resume x }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 33);
}

/// EH4.3b: a handle discharging TWO effects; `g` performs an op of each. Evidence for
/// both effects is threaded in canonical (effect-then-op) order. 10 + 20 = 30.
#[test]
fn eh43_multi_effect_direct_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn ge() -> i64; }\n\
        effect F { fn gf() -> i64; }\n\
        fn g() -> i64 ! { E, F } { let a = perform E.ge(); let b = perform F.gf(); return a + b; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { E.ge() => resume 10, F.gf() => resume 20 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 30);
}

/// EH4.3b × 4.3a: multi-effect PLUS propagation — `g` (effects E, F) calls one helper
/// performing E and one performing F; each forwards only the evidence for its own
/// effect. 10 + 20 = 30.
#[test]
fn eh43_multi_effect_propagation_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect E { fn ge() -> i64; }\n\
        effect F { fn gf() -> i64; }\n\
        fn he() -> i64 ! { E } { return perform E.ge(); }\n\
        fn hf() -> i64 ! { F } { return perform F.gf(); }\n\
        fn g() -> i64 ! { E, F } { let a = he(); let b = hf(); return a + b; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { E.ge() => resume 10, F.gf() => resume 20 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 30);
}

/// EH4.3b: a multi-effect handle mixing a SCOPED effect (`Reader`) and an ABORTIVE
/// effect (`Fail`), where `g` is the direct scrutinee (abortive can't propagate). The
/// canonical order is by effect name (`Fail` < `Reader`). g(-100): get resumes 5, then
/// the abort wins → 77.
#[test]
fn eh43_multi_effect_scoped_plus_abortive_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        effect Fail { fn raise() -> never; }\n\
        fn g(x: i64) -> i64 ! { Reader, Fail } { let a = perform Reader.get(); if x < 0 { perform Fail.raise(); } return a + x; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g(0 - 100) { Reader.get() => resume 5, Fail.raise() => 77 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 77);
}

/// EH4.1: a three-operation effect, exercising the sorted-op evidence ordering with
/// more than two clauses (and clauses written in a different order than sorted).
#[test]
fn eh41_three_op_effect_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Bus { fn a() -> i64; fn b() -> i64; fn c() -> i64; }\n\
        fn worker() -> i64 ! { Bus } { let x = perform Bus.c(); let y = perform Bus.a(); let z = perform Bus.b(); return x + y + z; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle worker() { Bus.b() => resume 200, Bus.a() => resume 30, Bus.c() => resume 4 }; return 0 - r; }\n";
    // c=>4, a=>30, b=>200; 4 + 30 + 200 = 234 (regardless of clause/perform order).
    assert_eq!(run_returning_negative(src), 234);
}

/// EH4.3a: a PURE helper called by an E-function is NOT an E-function and must stay
/// untouched (byte-identical, no evidence params); the program still runs. g performs
/// get→5, then calls the pure `double` → 10.
#[test]
fn eh43_pure_helper_not_threaded_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Reader { fn get() -> i64; }\n\
        fn double(x: i64) -> i64 { return x * 2; }\n\
        fn g() -> i64 ! { Reader } { let a = perform Reader.get(); return double(a); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { Reader.get() => resume 5 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 10);
}

// ── EH4.3c: abortive propagation via the EhResult discriminated-union return ───

/// EH4.3c: the abort propagates through an intermediate tail call. `g` does
/// `return helper(x)`; `helper` aborts on the error path. The abort threads up as an
/// `EhResult::Aborted` and the handle unwraps it → the clause value 88.
#[test]
fn eh43c_tail_propagation_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn helper(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { return helper(x); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g(0 - 7) { Fail.raise(m) => 88 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 88);
}

/// EH4.3c: the SAME chain on the non-error path returns the normal value (wrapped as
/// `Normal` and unwrapped) — `helper(5)` returns 5 through `g`.
#[test]
fn eh43c_tail_propagation_normal_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn helper(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { return helper(x); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g(5) { Fail.raise(m) => 88 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 5);
}

/// EH4.3c: a THREE-level tail-call chain `top → mid → deep`, only `deep` performs.
/// The abort propagates through both intermediate frames.
#[test]
fn eh43c_three_level_propagation_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        fn deep(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x; }\n\
        fn mid(x: i64) -> i64 ! { Fail } { return deep(x); }\n\
        fn top(x: i64) -> i64 ! { Fail } { return mid(x); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle top(0 - 3) { Fail.raise(m) => 123 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 123);
}

/// EH4.3c: the abortive op carries a parameter, and the clause computes from it —
/// `raise(code)` aborts, the clause resumes `code + 1` as the handle value.
#[test]
fn eh43c_propagation_with_binder_runs() {
    let src = "#[ring(outer)]\nmodule tool;\n\
        effect Fail { fn raise(code: i64) -> never; }\n\
        fn helper(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(41); } return x; }\n\
        fn g(x: i64) -> i64 ! { Fail } { return helper(x); }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g(0 - 1) { Fail.raise(code) => code + 1 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

// ── EH4.3d: same-ring cross-MODULE effect handlers (program-wide threading) ────

/// EH4.3d: the handler is in module `tool`, the performer in a separate same-ring
/// (outer) module `lib`. Evidence threads across the module boundary. → 42.
#[test]
fn eh43d_cross_module_scoped_runs() {
    let src = "#[ring(outer)]\nmodule lib;\n\
        effect Reader { fn get() -> i64; }\n\
        pub fn perform_it() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        #[ring(outer)]\nmodule tool;\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle lib::perform_it() { Reader.get() => resume 42 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.3d: cross-module scoped PROPAGATION — `g` (in `tool`) calls `leaf` (in `lib`),
/// which performs; evidence threads `tool::g` → `lib::leaf`. → 41 + 1 = 42.
#[test]
fn eh43d_cross_module_propagation_runs() {
    let src = "#[ring(outer)]\nmodule lib;\n\
        effect Reader { fn get() -> i64; }\n\
        pub fn leaf() -> i64 ! { Reader } { return perform Reader.get(); }\n\
        #[ring(outer)]\nmodule tool;\n\
        fn g() -> i64 ! { Reader } { let a = lib::leaf(); return a + 1; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle g() { Reader.get() => resume 41 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 42);
}

/// EH4.3d: cross-module DIRECT-abortive — the performer `parse` (in `lib`) aborts; the
/// handler is in `tool`. The abortive clause value becomes the handle value. → 77.
#[test]
fn eh43d_cross_module_abortive_runs() {
    let src = "#[ring(outer)]\nmodule lib;\n\
        effect Fail { fn raise(m: str) -> never; }\n\
        pub fn parse(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(\"neg\"); } return x * 2; }\n\
        #[ring(outer)]\nmodule tool;\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle lib::parse(0 - 5) { Fail.raise(m) => 77 }; return 0 - r; }\n";
    assert_eq!(run_returning_negative(src), 77);
}

/// EH4.3d ROOT-A regression: two same-ring modules each lower a *single-module* abortive
/// chain whose handle type `H` mangles identically (both `i64`). Each synthesizes a
/// `$eh_unwrap_i64` helper; before the fix both exported the bare name → duplicate wasm
/// export → non-validating module. With a module-qualified export name both coexist and
/// run: run1(-1) aborts → 1, run2(-1) aborts → 2, sum 3.
#[test]
fn eh43d_cross_module_same_h_abortive_runs() {
    let src = "#[ring(outer)]\nmodule a;\n\
        effect E1 { fn r() -> never; }\n\
        fn d1(x: i64) -> i64 ! { E1 } { if x < 0 { perform E1.r(); } return x; }\n\
        fn m1(x: i64) -> i64 ! { E1 } { return d1(x); }\n\
        pub fn run1(x: i64) -> i64 { let r = handle m1(x) { E1.r() => 1 }; return r; }\n\
        #[ring(outer)]\nmodule tool;\n\
        effect E2 { fn r() -> never; }\n\
        fn d2(x: i64) -> i64 ! { E2 } { if x < 0 { perform E2.r(); } return x; }\n\
        fn m2(x: i64) -> i64 ! { E2 } { return d2(x); }\n\
        fn run2(x: i64) -> i64 { let r = handle m2(x) { E2.r() => 2 }; return r; }\n\
        pub fn tool_main(i: i64, l: i64) -> i64 { let a = a::run1(0 - 1); let b = run2(0 - 1); return 0 - (a + b); }\n";
    assert_eq!(run_returning_negative(src), 3);
}
