//! PR-0: monomorphized generic-impl methods must carry their DECLARED effect
//! row. The monomorphizer built mono methods with `EffectSet::empty()`
//! (`type_check/expressions.rs:3271`), so a generic impl method calling an
//! effect-gated intrinsic (`alloc`) either (a) spuriously tripped E001 on its
//! own monomorphized body, or (b) let callers escape the effect requirement —
//! an unsound under-approximation of the capability surface. `Vec<T>::push`
//! is the first feature to hit this; fixed by propagating the declared row.

use sigil_compiler::compile_named_module;

fn diag_codes(src: &str) -> Result<(), Vec<String>> {
    match compile_named_module("m.sigil".to_string(), src.to_string()) {
        Ok(_) => Ok(()),
        Err(e) => Err(e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect()),
    }
}

// A generic impl method that declares `! { Alloc }` and calls the `alloc`
// intrinsic. Monomorphized when `make` is called on a concrete `Box<i64>`.
const GENERIC_IMPL_ALLOC: &str = r#"
#[ring(outer)] #[trusted]
module m;

effect Alloc;

record Box<T> { p: T }

impl Box<T> {
    pub fn make(self: Box<T>) -> i64 ! { Alloc } {
        return alloc(8);
    }
}
"#;

#[test]
fn generic_impl_method_calling_alloc_compiles_when_caller_declares_effect() {
    // The mono'd `make__i64` body calls `alloc`; with its declared `Alloc`
    // row propagated, this compiles cleanly. (Before the fix: spurious E001
    // on the monomorphized body, whose row was empty.)
    let src = format!(
        "{GENERIC_IMPL_ALLOC}\n\
         pub fn run() -> i64 ! {{ Alloc }} {{\n\
         \x20   let b: Box<i64> = Box {{ p: 0 }};\n\
         \x20   return b.make();\n\
         }}\n"
    );
    if let Err(codes) = diag_codes(&src) {
        panic!("expected clean compile, got diagnostics: {codes:?}");
    }
}

#[test]
fn generic_impl_method_alloc_forces_caller_to_declare_effect() {
    // Soundness direction: a PURE caller (`! { }`) that calls a method
    // requiring `Alloc` MUST be rejected with E001. (Before the fix the
    // mono method's empty row let the caller escape the requirement.)
    let src = format!(
        "{GENERIC_IMPL_ALLOC}\n\
         pub fn run() -> i64 ! {{ }} {{\n\
         \x20   let b: Box<i64> = Box {{ p: 0 }};\n\
         \x20   return b.make();\n\
         }}\n"
    );
    let codes = diag_codes(&src).expect_err("pure caller of an Alloc method must be rejected");
    assert!(
        codes.iter().any(|c| c == "E001"),
        "expected E001 (undeclared effect Alloc), got: {codes:?}"
    );
}

// ── The NON-generic twin (the mod.rs emission site) ──────────────────────────
//
// PR-0 fixed the monomorphized path but left `Item::ImplDef`'s non-generic
// emission at `effects: EffectSet::empty()` — so EVERY non-generic impl-method
// call site escaped the effect requirement (effect_check reads the callee
// TypedFunction's row; empty ⊆ any caller). Surfaced by the T156
// local-shadows-module adversarial review; fixed by mirroring PR-0
// (`resolve_effect_row(&method.effects, &universe)`).

const NON_GENERIC_IMPL_DANGER: &str = r#"
#[ring(outer)]
module m;

effect Danger;

record Cell { p: i64 }

impl Cell {
    pub fn boom(self: Cell) -> i64 ! { Danger } {
        return 0;
    }
}
"#;

#[test]
fn non_generic_impl_method_effect_row_forces_caller_to_declare() {
    // Soundness: a pure caller (`! { }`) of a non-generic `! { Danger }`
    // method MUST be rejected E001. Before the fix this compiled CLEAN —
    // the effect launder through every non-generic method call.
    let src = format!(
        "{NON_GENERIC_IMPL_DANGER}\n\
         pub fn run() -> i64 ! {{ }} {{\n\
         \x20   let b: Cell = Cell {{ p: 1 }};\n\
         \x20   return b.boom();\n\
         }}\n"
    );
    let codes = diag_codes(&src).expect_err("pure caller of a Danger method must be rejected");
    assert!(
        codes.iter().any(|c| c == "E001"),
        "expected E001 (undeclared effect Danger), got: {codes:?}"
    );
}

#[test]
fn non_generic_impl_method_effect_row_compiles_when_caller_declares() {
    let src = format!(
        "{NON_GENERIC_IMPL_DANGER}\n\
         pub fn run() -> i64 ! {{ Danger }} {{\n\
         \x20   let b: Cell = Cell {{ p: 1 }};\n\
         \x20   return b.boom();\n\
         }}\n"
    );
    if let Err(codes) = diag_codes(&src) {
        panic!("expected clean compile, got diagnostics: {codes:?}");
    }
}

#[test]
fn shadowed_local_method_call_still_effect_checked() {
    // The T156 local-wins resolution commits a `.`-spelled call whose local
    // shadows a module name — the committed node must be identical to an
    // ordinary local method call for the DOWNSTREAM effect pass: a pure
    // caller invoking an effectful method through the shadowed spelling must
    // still be E001-rejected (no effect launder through the commit path).
    let src = r#"
#[ring(outer)]
module cellmod;
pub fn unrelated(x: i64) -> i64 { return x; }

#[ring(outer)]
module main;
use sigil::cellmod;

effect Danger;

record Cell { p: i64 }

impl Cell {
    pub fn boom(self: Cell) -> i64 ! { Danger } {
        return 0;
    }
}

pub fn run() -> i64 ! { } {
    let cellmod: Cell = Cell { p: 1 };
    return cellmod.boom();
}
"#;
    let codes = diag_codes(src)
        .expect_err("pure caller of a Danger method via a shadowed name must be rejected");
    assert!(
        codes.iter().any(|c| c == "E001"),
        "expected E001 through the shadowed-local commit path, got: {codes:?}"
    );
}
