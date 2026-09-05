//! Capabilities-as-values: the `mint <Cap> for <target>` constructor.
//!
//! `mint` is the privileged constructor that makes capabilities first-class
//! VALUES (creation), composing with the existing delegation (`send`, linear
//! move) and attenuation (`.restrict`) machinery. This suite pins the
//! type-check surface of the constructor:
//!   - T272: `mint` of a non-mintable / undeclared cap type (fail-closed).
//!   - T273: a `mint` site that does not hold the minting authority (the gate).
//!   - T277: `mint … for <target>` where the target is not a nominal resource.
//!   - clean compiles for the well-formed constructor (authority held); the
//!     `mint`→`restrict`→full-sink C003 (mint composes with the existing rule).

use sigil_compiler::{CompileOptions, compile_named_module, compile_named_module_with_options};

/// `Admin` is an authority cap (non-mintable); `FileAccess` declares it as its
/// minting authority; `Approval` is a parametric (deadline-typed) mintable cap
/// for the static revocation-by-expiry tests; `File` is the resource minted FOR.
const PRELUDE: &str = "module sigil;\n\
cap type Admin { mint_file }\n\
cap type FileAccess mintable_by Admin { read, write }\n\
cap type Approval(deadline: i64) mintable_by Admin { ok }\n\
record File { id: i64 }\n";

/// Compile `PRELUDE + body`; return the sorted, de-duplicated emitted codes
/// (empty = compiled cleanly).
fn codes(body: &str) -> Vec<String> {
    match compile_named_module("cap_mint.sigil", format!("{PRELUDE}{body}")) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut cs: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            cs.sort();
            cs.dedup();
            cs
        }
    }
}

fn assert_rejects_with(body: &str, code: &str) {
    let cs = codes(body);
    assert!(
        cs.iter().any(|c| c == code),
        "expected {code} for `{body}`, got {cs:?}"
    );
}

fn assert_clean(body: &str) {
    let cs = codes(body);
    assert!(
        cs.is_empty(),
        "expected clean compile for `{body}`, got {cs:?}"
    );
}

/// Like `codes`, but with a `--build-deadline` reference instant set.
fn codes_with(body: &str, build_deadline: i64) -> Vec<String> {
    let opts = CompileOptions {
        build_deadline: Some(build_deadline),
    };
    match compile_named_module_with_options("cap_mint.sigil", format!("{PRELUDE}{body}"), opts) {
        Ok(_) => Vec::new(),
        Err(e) => {
            let mut cs: Vec<String> = e
                .diagnostics()
                .iter()
                .map(|d| d.code().as_str().to_owned())
                .collect();
            cs.sort();
            cs.dedup();
            cs
        }
    }
}

// ── `mint` is a CONTEXTUAL keyword, not reserved ────────────────────────────

#[test]
fn mint_is_usable_as_an_ordinary_identifier() {
    // `mint` is special ONLY in `mint <CapType> …` (two identifiers); everywhere
    // else it is a plain identifier. This is load-bearing: an ERC20 `function
    // mint` translates through the Solidity frontend to `fn mint`, which must
    // still parse and compile. Exercises mint as a fn name, a call, and a local.
    assert_clean(
        "fn mint(x: i64) -> i64 { return x; }\n\
         fn g() -> i64 { let m = mint(7); let mint = 5; return m + mint; }\n",
    );
}

// ── clean: the constructor type-checks and lowers (holding the authority) ───

#[test]
fn mint_constructs_a_capability_value() {
    // The minting authority `&Admin` is in scope, so the gate is satisfied.
    assert_clean(
        "fn make(f: File, admin: &Admin) -> FileAccess { return mint FileAccess for f; }\n",
    );
}

#[test]
fn mint_then_delegate_via_call() {
    // A freshly-minted cap carries full authority, so it discharges the
    // full-authority Call sink — the static form of "delegate the capability".
    assert_clean(
        "fn use_cap(c: FileAccess) -> i64 { return 1; }\n\
         fn make(f: File, admin: &Admin) -> i64 { let c = mint FileAccess for f; return use_cap(c); }\n",
    );
}

// Note on delegation: `mint_then_delegate_via_call` above exercises the
// full-authority cap sink that delegation relies on — a freshly-minted cap
// discharges it. Actor `send`-delegation (`recipient.send(Grant(cap))`) routes
// the same minted cap through the identical message-serialization full-authority
// sink; it additionally requires actor-state authority plumbing (the minting
// authority is not a sendable handler parameter), which is orthogonal to `mint`.

// ── T273: the minting authority gate is fail-closed ─────────────────────────

#[test]
fn mint_without_authority_is_t273() {
    // No `&Admin` in scope → the gate rejects the mint before AIR.
    assert_rejects_with(
        "fn make(f: File) -> FileAccess { return mint FileAccess for f; }\n",
        "T273",
    );
}

// C003 is a Z3 (solver) diagnostic — gated to the `solver` feature so the
// `--no-default-features` build (solver off, no Z3 verifier) doesn't expect it.
#[cfg(feature = "solver")]
#[test]
fn mint_then_restrict_then_sink_is_c003() {
    // Attenuation (`.restrict`) narrows authority; passing the narrowed cap to a
    // full-authority sink (here, the return-value sink) is the EXISTING C003
    // rule — `mint` composes with it, it does not weaken it.
    assert_rejects_with(
        "fn make(f: File, admin: &Admin) -> FileAccess { let c = mint FileAccess for f; return c.restrict(read); }\n",
        "C003",
    );
}

// ── T272: mintability is fail-closed ────────────────────────────────────────

#[test]
fn mint_of_policyless_cap_is_t272() {
    // `Admin` is a declared cap type but declares no `mintable_by` policy.
    assert_rejects_with(
        "fn bad(f: File) -> Admin { return mint Admin for f; }\n",
        "T272",
    );
}

#[test]
fn mint_of_undeclared_cap_is_t272() {
    assert_rejects_with(
        "fn bad(f: File) -> i64 { let c = mint Nope for f; return 0; }\n",
        "T272",
    );
}

// ── M4: deadline-aware mint (static revocation-by-expiry) ───────────────────

#[test]
fn mint_parametric_deadline_in_future_is_clean() {
    // `mint Approval(2030) for f` with build-deadline 2025: 2030 >= 2025, fresh.
    // Routed through a fresh-deadline Call sink (so the only deadline under test
    // is the mint's, not a return-type annotation).
    let cs = codes_with(
        "fn use_approval(c: Approval(2030)) -> i64 { return 1; }\n\
         fn make(f: File, admin: &Admin) -> i64 { let c = mint Approval(2030) for f; return use_approval(c); }\n",
        2025,
    );
    assert!(cs.is_empty(), "expected clean, got {cs:?}");
}

#[test]
fn mint_parametric_stale_deadline_is_t199() {
    // `mint Approval(2020)` with build-deadline 2025: the cap is already past at
    // build time — static revocation-by-expiry rejects it before any execution.
    // The minted `Approval(2020)` is the ONLY place the stale deadline appears
    // (un-annotated let, no sink annotation), so this exercises the mint's own
    // T199 path — not a type annotation's.
    let cs = codes_with(
        "fn make(f: File, admin: &Admin) -> i64 { let c = mint Approval(2020) for f; return 0; }\n",
        2025,
    );
    assert!(cs.iter().any(|c| c == "T199"), "expected T199, got {cs:?}");
}

#[test]
fn mint_nonparametric_with_deadline_is_t197() {
    // `FileAccess` is non-parametric; supplying a deadline literal is T197.
    assert_rejects_with(
        "fn bad(f: File, admin: &Admin) -> i64 { let c = mint FileAccess(2030) for f; return 0; }\n",
        "T197",
    );
}

#[test]
fn mint_parametric_without_deadline_is_t196() {
    // `Approval` is parametric; omitting the deadline literal is T196.
    assert_rejects_with(
        "fn bad(f: File, admin: &Admin) -> i64 { let c = mint Approval for f; return 0; }\n",
        "T196",
    );
}

// ── T277: the target must be a nominal resource ─────────────────────────────

#[test]
fn mint_for_primitive_target_is_t277() {
    assert_rejects_with(
        "fn bad(n: i64, admin: &Admin) -> FileAccess { return mint FileAccess for n; }\n",
        "T277",
    );
}
