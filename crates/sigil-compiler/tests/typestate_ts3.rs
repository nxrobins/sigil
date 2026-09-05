//! TS3 of the typestate epic — state-polymorphic operations.
//!
//! A `fn op<@S>(f: File<S>)` is generic over the protocol STATE: `@S` is a
//! state-kinded binder, used as `File<S>`, that binds to a concrete marker at the
//! call site by reusing the generic unify/subst channel. So one state-agnostic op
//! serves every state, and the binding can flow from an argument, the expected
//! return type, or alongside ordinary type parameters. State args ERASE from the
//! mono key — a state-polymorphic fn collapses to ONE instance regardless of state,
//! so the byte-identical-AIR gate (TS0) is undisturbed.
//!
//! (Returning a typestate VALUE that is the consumed input param by value is subject
//! to the same linear-escape rule as capabilities — a mutation-capability
//! interaction, NOT a state-polymorphism gap; out of scope here. State threads fine
//! through a constructed/return-typed result, exercised below.)

use sigil_compiler::compile_tool;

const PROTO: &str = "\
state File { Open, Closed }\n\
record File<@S> { fd: i64 }\n\
fn open() -> File<Open> { return File { fd: 1 }; }\n\
fn shut(f: File<Open>) -> File<Closed> { return File { fd: 0 }; }\n\
fn fd<@S>(f: File<S>) -> i64 { return f.fd; }\n\
fn fresh<@S>() -> File<S> { return File { fd: 0 }; }\n\
fn dup<T, @S>(x: T, f: File<S>) -> i64 { return f.fd; }\n\
fn need_closed(f: File<Closed>) -> i64 { return f.fd; }\n";

fn err_codes(src: &str) -> Vec<String> {
    match compile_tool(src) {
        Ok(_) => vec![],
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn main_body(stmts: &str) -> String {
    format!(
        "module tool;\n{PROTO}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{stmts}}}\n"
    )
}

#[test]
fn state_polymorphic_accessor_over_two_states() {
    // One generic `fd` called on BOTH `File<Open>` and `File<Closed>` — `@S` binds
    // per call site (from the argument). The two instantiations collapse to one
    // erased instance.
    let cs = err_codes(&main_body(
        "    let a: File<Open> = open();\n\
         \x20   let x: i64 = fd(a);\n\
         \x20   let b: File<Closed> = shut(open());\n\
         \x20   let y: i64 = fd(b);\n\
         \x20   return x + y;\n",
    ));
    assert!(
        cs.is_empty(),
        "a state-polymorphic accessor over two states should compile; got {cs:?}"
    );
}

#[test]
fn state_poly_binding_flows_from_return_type() {
    // `fresh<@S>() -> File<S>` has no argument to fix `@S`; it binds from the
    // EXPECTED type (the let annotation `File<Open>`).
    let cs = err_codes(&main_body(
        "    let a: File<Open> = fresh();\n\
         \x20   let n: i64 = fd(a);\n\
         \x20   return n;\n",
    ));
    assert!(
        cs.is_empty(),
        "a state-polymorphic op binding `@S` from the return type should compile; got {cs:?}"
    );
}

#[test]
fn state_and_ordinary_generics_compose() {
    // `dup<T, @S>` mixes an ordinary type param `T` with a state param `@S`. The
    // ordinary arg keeps its place in the mono key; the state arg erases (so
    // `dup<i64, Open>` and `dup<i64, Closed>` share one instance).
    let cs = err_codes(&main_body(
        "    let a: File<Open> = open();\n\
         \x20   let x: i64 = dup(7, a);\n\
         \x20   let b: File<Closed> = shut(open());\n\
         \x20   let y: i64 = dup(9, b);\n\
         \x20   return x + y;\n",
    ));
    assert!(
        cs.is_empty(),
        "state + ordinary generics should compose; got {cs:?}"
    );
}

#[test]
fn state_polymorphic_impl_method_compiles() {
    // Regression (adversarial sweep): a state-poly impl method on a stateful
    // receiver used to ICE — `build_mono_impl_method_mangled_name` mangled the
    // receiver's `StateMarker` arg, hitting `mangle_type`'s fail-closed ICE backstop.
    // The state-blind filter now drops it, so the method works over any state and the
    // two dispatches collapse to one erased instance.
    let cs = err_codes(
        "module tool;\n\
         state File { Open, Closed }\n\
         record File<@S> { fd: i64 }\n\
         fn open() -> File<Open> { return File { fd: 1 }; }\n\
         fn shut(f: File<Open>) -> File<Closed> { return File { fd: 0 }; }\n\
         impl File<@S> { pub fn peek(self: File<S>) -> i64 { return self.fd; } }\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
         \x20   let a: File<Open> = open();\n\
         \x20   let x: i64 = a.peek();\n\
         \x20   let b: File<Closed> = shut(open());\n\
         \x20   let y: i64 = b.peek();\n\
         \x20   return x + y;\n\
         }\n",
    );
    assert!(
        cs.is_empty(),
        "a state-polymorphic impl method should compile (was an ICE); got {cs:?}"
    );
}

#[test]
fn state_poly_does_not_erase_the_protocol_check() {
    // `fresh::<Open>` (via the annotation) yields `File<Open>`, so calling the
    // `Closed`-only `need_closed` on it is still a wrong-state T266 — `@S` resolved
    // to the ACTUAL state, not a wildcard that voids the protocol check.
    let cs = err_codes(&main_body(
        "    let a: File<Open> = fresh();\n\
         \x20   let n: i64 = need_closed(a);\n\
         \x20   return n;\n",
    ));
    assert!(
        cs.iter().any(|c| c == "T266"),
        "a wrong-state call on a state-poly result must still be T266; got {cs:?}"
    );
}
