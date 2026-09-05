//! PR-3b of the trait epic — bound ENFORCEMENT (the type-check side).
//!
//! At a generic instantiation site the bound check (`type_satisfies_trait` via
//! `check_bounds`) runs with the concrete type-args in hand, BEFORE the body is
//! monomorphized. v1 sources impls from the closed built-in table — `i64` /
//! `str` / `bool` × `Hash` / `Eq` — so those primitives satisfy the bounds and a
//! user `record` does not (structural satisfaction is PR-4). A bound naming an
//! undeclared trait is T248.
//!
//! These bodies do NOT call the trait methods — the primitive `.hash()`/`.eq()`
//! LOWERING (so `k.hash()` works in a body) is PR-3c. Here we only exercise the
//! satisfaction predicate + the accept/reject decision. Traits are declared
//! inline (ambient injection of a stdlib `traits` module is also PR-3c).

use sigil_compiler::compile_tool;

const TRAITS: &str = "trait Hash { fn hash(self: Self) -> i64; }\n\
                      trait Eq { fn eq(self: Self, other: Self) -> bool; }\n";

/// `module tool;` + the trait decls + caller-supplied defs + a `tool_main`.
fn prog(defs: &str, body: &str) -> String {
    format!(
        "module tool;\n{TRAITS}{defs}\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn compiles(src: &str) -> bool {
    compile_tool(src).is_ok()
}

/// True iff compilation fails AND the given diagnostic code appears.
fn fails_with(src: &str, code: &str) -> bool {
    match compile_tool(src) {
        Ok(_) => false,
        Err(e) => format!("{e:?}").contains(code),
    }
}

// ── built-in impls: primitives satisfy Hash / Eq ─────────────────────────────

#[test]
fn hash_bound_accepts_str() {
    let src = prog(
        "fn keyed<T: Hash>(x: T) -> i64 { return 0; }",
        "    let s: str = \"hi\";\n    let r: i64 = keyed(s);\n    return 0 - 1;",
    );
    assert!(compiles(&src), "str satisfies Hash via the built-in impl");
}

#[test]
fn hash_bound_accepts_i64() {
    let src = prog(
        "fn keyed<T: Hash>(x: T) -> i64 { return 0; }",
        "    let n: i64 = 5;\n    let r: i64 = keyed(n);\n    return 0 - 1;",
    );
    assert!(compiles(&src), "i64 satisfies Hash via the built-in impl");
}

#[test]
fn hash_bound_accepts_bool() {
    let src = prog(
        "fn keyed<T: Hash>(x: T) -> i64 { return 0; }",
        "    let b: bool = true;\n    let r: i64 = keyed(b);\n    return 0 - 1;",
    );
    assert!(compiles(&src), "bool satisfies Hash via the built-in impl");
}

#[test]
fn composed_bound_accepts_str() {
    let src = prog(
        "fn keyed<K: Hash + Eq>(x: K) -> i64 { return 0; }",
        "    let s: str = \"hi\";\n    let r: i64 = keyed(s);\n    return 0 - 1;",
    );
    assert!(compiles(&src), "str satisfies both Hash AND Eq");
}

// ── rejection: a user record has no impl yet (structural is PR-4) ─────────────

#[test]
fn hash_bound_rejects_record_with_t245() {
    let src = prog(
        "record NoHash { v: i64 }\nfn keyed<T: Hash>(x: T) -> i64 { return 0; }",
        "    let n: NoHash = NoHash { v: 1 };\n    let r: i64 = keyed(n);\n    return 0 - 1;",
    );
    assert!(
        fails_with(&src, "T245"),
        "a record without an impl must be rejected with T245"
    );
}

#[test]
fn composed_bound_rejects_record_with_t245() {
    // Fails on the first unsatisfied bound (`Hash`).
    let src = prog(
        "record NoHash { v: i64 }\nfn keyed<K: Hash + Eq>(x: K) -> i64 { return 0; }",
        "    let n: NoHash = NoHash { v: 1 };\n    let r: i64 = keyed(n);\n    return 0 - 1;",
    );
    assert!(fails_with(&src, "T245"));
}

// ── unknown trait in a bound → T248 ──────────────────────────────────────────

#[test]
fn unknown_trait_in_bound_with_t248() {
    // `Bogus` is never declared.
    let src = prog(
        "fn keyed<T: Bogus>(x: T) -> i64 { return 0; }",
        "    let s: str = \"hi\";\n    let r: i64 = keyed(s);\n    return 0 - 1;",
    );
    assert!(
        fails_with(&src, "T248"),
        "a bound naming an undeclared trait must be T248"
    );
}

// ── an UNBOUNDED generic accepts anything (no check) ─────────────────────────

#[test]
fn unbounded_generic_accepts_record() {
    // No bound ⇒ no satisfaction check ⇒ a record is fine.
    let src = prog(
        "record Anything { v: i64 }\nfn idy<T>(x: T) -> i64 { return 0; }",
        "    let a: Anything = Anything { v: 1 };\n    let r: i64 = idy(a);\n    return 0 - 1;",
    );
    assert!(
        compiles(&src),
        "an unbounded generic places no trait obligation"
    );
}

// ── a declared-but-uninstantiated bad bound is NOT an error (AG-T4) ───────────

#[test]
fn uninstantiated_bad_bound_is_not_checked() {
    // `keyed` is declared with an unsatisfiable-by-record bound but never called
    // — bounds are enforced at INSTANTIATION, so this compiles.
    let src = prog(
        "record NoHash { v: i64 }\nfn keyed<T: Hash>(x: T) -> i64 { return 0; }",
        "    return 0 - 1;",
    );
    assert!(
        compiles(&src),
        "a never-instantiated bounded generic is not bound-checked (AG-T4)"
    );
}
