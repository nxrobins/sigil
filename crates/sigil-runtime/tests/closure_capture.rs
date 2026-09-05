//! Closure environment capture — RUNTIME value-correctness.
//!
//! A closure captures its free variables BY VALUE into a heap `__env` struct
//! (`[table_idx: i32 @0, captures @4+]`); the lambda-lifted body must read each
//! capture back out of `__env` (param 0) before use. A regression here is
//! SILENT: the capture local reads as an uninitialized 0, so `x + k` with k=10
//! quietly computes `x + 0`. These tests pin the read by asserting the exact
//! VALUE — the three differential gates check types/nodes, never runtime bytes,
//! and no prior test executed a capturing closure with a value assertion (which
//! is exactly why the bug was latent). Harness mirrors `bounded_map.rs`'s
//! negative-sentinel decode, but takes a FULL module (some fixtures need
//! top-level records/impls/fns).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

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
            let p = "tool returned error (";
            let s = message
                .find(p)
                .unwrap_or_else(|| panic!("no sentinel in: {message}"))
                + p.len();
            let e = message[s..].find(')').unwrap();
            message[s..s + e].parse().unwrap()
        }
        other => panic!("expected sentinel trap, got {other:?}"),
    }
}

// A capturing closure bound to a LOCAL, called directly. x=5, k=10 → 15.
#[test]
fn capture_in_local_direct_call() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let k: i64 = 10;\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x + k; };\n\
        \x20   return 0 - g(5);\n\
        }\n";
    assert_eq!(neg(src), 15, "captured `k` must be 10, not 0");
}

// A capturing closure passed as a fn ARG, then invoked. x=5, k=10 → 15.
#[test]
fn capture_passed_as_arg() {
    let src = "module tool;\n\
        fn apply(g: Fn(i64) -> i64, x: i64) -> i64 { return g(x); }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let k: i64 = 10;\n\
        \x20   return 0 - apply(fn(x: i64) -> i64 { return x + k; }, 5);\n\
        }\n";
    assert_eq!(neg(src), 15);
}

// Pure-capture closure (no param use), invoked repeatedly in a loop. base=10 ×3 → 30.
#[test]
fn capture_only_read_in_loop() {
    let src = "module tool;\n\
        fn apply3(g: Fn(i64) -> i64) -> i64 {\n\
        \x20   let mut acc: i64 = 0;\n\
        \x20   let mut i: i64 = 0;\n\
        \x20   while i < 3 { acc = acc + g(i); i = i + 1; }\n\
        \x20   return acc;\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let base: i64 = 10;\n\
        \x20   return 0 - apply3(fn(x: i64) -> i64 { return base; });\n\
        }\n";
    assert_eq!(neg(src), 30);
}

// TWO captures — pins the per-capture offset accumulation (a @ off 4, b @ off 12).
// x=1, a=3, b=4 → 8. A wrong stride would read b from a's slot or garbage.
#[test]
fn two_captures_offset_accumulation() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let a: i64 = 3;\n\
        \x20   let b: i64 = 4;\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x + a + b; };\n\
        \x20   return 0 - g(1);\n\
        }\n";
    assert_eq!(neg(src), 8, "both captures must read at their own offset");
}

// A capturing closure STORED in a generic record field, retrieved, called.
// This is the path that makes lazy iterator adapters (MapIter { inner, f })
// viable — the closure survives field storage + `let g = self.f` retrieval.
#[test]
fn capture_stored_in_generic_field() {
    let src = "module tool;\n\
        record Holder<F> { f: F }\n\
        impl Holder<F> {\n\
        \x20   pub fn run(self: Holder<F> @Mut, x: i64) -> i64 { let g = self.f; return g(x); }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let k: i64 = 10;\n\
        \x20   let h: Holder<Fn(i64) -> i64> = Holder { f: fn(x: i64) -> i64 { return x + k; } };\n\
        \x20   return 0 - h.run(5);\n\
        }\n";
    assert_eq!(neg(src), 15);
}

// CONTROL — a capture-FREE closure must still compute correctly (guards the fix
// from perturbing the no-capture path: its entry prologue is empty). x=5 → 10.
#[test]
fn no_capture_closure_unaffected() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x + x; };\n\
        \x20   return 0 - g(5);\n\
        }\n";
    assert_eq!(neg(src), 10);
}

// MIXED WIDTHS — an i32 capture (width 4) followed by an i64 capture (width 8):
// pins that the offset stride is per-capture `width()`, not a fixed 8. a@off4,
// b@off8. x=1, a=7, b=100 → 108. A fixed-8 stride would read b from garbage.
#[test]
fn mixed_width_captures() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let a: i32 = 7;\n\
        \x20   let b: i64 = 100;\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x + a.as_i64() + b; };\n\
        \x20   return 0 - g(1);\n\
        }\n";
    assert_eq!(neg(src), 108);
}

// bool capture (width 4) read in a branch condition. flag=true → returns x=5.
#[test]
fn bool_capture() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let flag: bool = true;\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { if flag { return x; } else { return 0 - x; } };\n\
        \x20   return 0 - g(5);\n\
        }\n";
    assert_eq!(neg(src), 5);
}

// str capture (a Ptr, width 4): the captured handle must still point at the data.
// byte_at(0) of "hi" = 104 ('h').
#[test]
fn str_capture() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let s: str = \"hi\";\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return s.byte_at(0); };\n\
        \x20   return 0 - g(0);\n\
        }\n";
    assert_eq!(neg(src), 104);
}

// THREE i64 captures — offset accumulation across more than two. x=10 → 16.
#[test]
fn three_captures() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let a: i64 = 1;\n\
        \x20   let b: i64 = 2;\n\
        \x20   let c: i64 = 3;\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x + a + b + c; };\n\
        \x20   return 0 - g(10);\n\
        }\n";
    assert_eq!(neg(src), 16);
}

// A closure inside an IMPL METHOD body, capturing a method local. m.go(5), k=10 → 15.
#[test]
fn capture_in_impl_method() {
    let src = "module tool;\n\
        record W { base: i64 }\n\
        impl W {\n\
        \x20   pub fn go(self: W @Mut, x: i64) -> i64 {\n\
        \x20       let k: i64 = 10;\n\
        \x20       let g: Fn(i64) -> i64 = fn(z: i64) -> i64 { return z + k; };\n\
        \x20       return g(x);\n\
        \x20   }\n\
        }\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut w: W = W { base: 0 };\n\
        \x20   return 0 - w.go(5);\n\
        }\n";
    assert_eq!(neg(src), 15);
}

// Capture is BY VALUE: capturing k=10 then reassigning k=99 before the call must
// still see 10 (the value at capture time), not 99. g(5) → 15, never 104.
#[test]
fn capture_is_by_value() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let mut k: i64 = 10;\n\
        \x20   let g: Fn(i64) -> i64 = fn(x: i64) -> i64 { return x + k; };\n\
        \x20   k = 99;\n\
        \x20   return 0 - g(5);\n\
        }\n";
    assert_eq!(neg(src), 15, "capture is by value at construction time");
}

// NESTED closures — a closure whose body itself defines another CAPTURING closure.
// `inner` transitively captures `k` (tool_main local → `outer`'s env → `inner`'s env).
// This pins that lambda-lifting assigns the inner closure a DISTINCT synthesized
// function id: because the parent closure's slot was not reserved before its body
// (and the nested closure inside it) was checked, BOTH closures were named
// `tool::__closure_N`. `function_ids` is keyed by name, so the inner closure's
// construct resolved to the OUTER function — making `inner(y)` re-invoke `outer`,
// which infinite-recurses (wasm stack overflow). outer(5) → inner(5) → 5 + k(=10) = 15.
#[test]
fn nested_closure_transitive_capture() {
    let src = "module tool;\n\
        pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
        \x20   let k: i64 = 10;\n\
        \x20   let outer: Fn(i64) -> i64 = fn(y: i64) -> i64 {\n\
        \x20       let inner: Fn(i64) -> i64 = fn(z: i64) -> i64 { return z + k; };\n\
        \x20       return inner(y);\n\
        \x20   };\n\
        \x20   return 0 - outer(5);\n\
        }\n";
    assert_eq!(
        neg(src),
        15,
        "inner closure must target its own function, not recurse into outer"
    );
}
