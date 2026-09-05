//! Taint soundness at the `spawn` message boundary (docs/specs/taint-join-soundness.md, D2 / #253).
//!
//! FOUND BY AN INDEPENDENT REVIEW, not this project's own audit. `spawn` is the THIRD actor message
//! boundary — `send` and `ask` deliver a payload to a handler's params; `spawn` delivers its args to
//! the spawned actor's `init` params. The F007 fix wired a `can_flow_to` sink for `send`/`ask`
//! (`check_message_payload_taint`, taint_check.rs) but `spawn` was left as
//! `TypedExprKind::Spawn(_) => TaintLabel::Public` — the `_` discards the payload entirely. So a
//! `@Secret` value crossing into a `@Public` `init` param is silently laundered, exactly as the
//! `send` hole was before F007.
//!
//! WHY A CAPABILITY, NOT A SCALAR. `spawn` init arguments must be capability-typed (T096,
//! capability_tc.rs) — a bare `i64 @Secret` cannot even reach `spawn`. The reachable laundering is a
//! `@Secret`-tainted CAPABILITY flowing into a lower-taint init param. The taint annotation rides on
//! the cap value (a handler param `f: Fuel @Secret`), so the leak is a real, typeable program.
//!
//! THE MODEL, grounded (taint_check.rs):
//!   * `send`/`ask` compute per-arg taints and call `check_message_payload_taint`, which rejects any
//!     arg whose taint cannot flow to the receiving handler param's declared taint (T001), and
//!     rejects any `@SecretCT` payload wholesale at the actor boundary (T028 / CT014).
//!   * `spawn` must mirror both: its args flow to `TypedFunctionKind::ActorInit` params.
//!   * every rejection assertion below pins the SPAWN sink's message ("cannot spawn @…"), not the
//!     bare code, so a program rejected for some unrelated reason does not count as a pass — the test
//!     is tied to the spawn boundary, not to rejection-in-general.

use sigil_compiler::CompileError;
use sigil_compiler::compile_named_module;

/// The distinctive fragment of the spawn-sink T001 message. Pinning this rather than the bare code
/// "T001" ties every rejection assertion to the sink we mean: a leak caught elsewhere (a `let`
/// downgrade, a return sink, a T096 type error) carries a different message and does NOT satisfy it.
const SPAWN_SINK_MSG: &str = "cannot spawn @";

fn err_debug(e: &CompileError) -> String {
    format!("{e:?}")
}

/// A spawn that launders a tainted cap into a lower-taint `init` param MUST be rejected at the spawn
/// sink. Before the fix this panics "SOUNDNESS HOLE" (the program compiles — the payload is never
/// visited). After the fix it is rejected with the spawn-sink message.
fn assert_spawn_leak_rejected(name: &str, source: &str, why: &str) {
    match compile_named_module(name, source) {
        Ok(_) => panic!("SOUNDNESS HOLE: {why}\n--- source ---\n{source}"),
        Err(e) => {
            let d = err_debug(&e);
            assert!(
                d.contains(SPAWN_SINK_MSG),
                "rejected, but NOT at the spawn sink — the test is not measuring the spawn boundary.\n\
                 wanted a message containing: {SPAWN_SINK_MSG:?}\ngot: {d}\n--- source ---\n{source}"
            );
        }
    }
}

fn assert_compiles(name: &str, source: &str, why: &str) {
    if let Err(e) = compile_named_module(name, source) {
        panic!(
            "{why}\ngot rejection: {}\n--- source ---\n{source}",
            err_debug(&e)
        );
    }
}

// ── The core hole: @Secret cap → @Public init param ──────────────────────────────────────────────

/// A `@Secret`-tainted `Fuel` cap spawned into `Worker.init(f: Fuel)` (default @Public) must be
/// REJECTED. This is the exact leak #253 describes: currently ACCEPTED (spawn returns Public,
/// discarding the payload).
#[test]
fn spawn_secret_cap_into_public_init_is_rejected() {
    assert_spawn_leak_rejected(
        "spawn_secret.sigil",
        r#"module sigil;
cap type Fuel {}
actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}
entry actor Main {
    on Leak(f: Fuel @Secret) -> i64 {
        let w = spawn::<Worker>(f);
        return 0;
    }
}
"#,
        "a @Secret cap spawned into a @Public init param is laundered across the actor boundary",
    );
}

/// The @Internal case. A test written from the same mental model as the fix inherits the fix's blind
/// spot — @Secret-only examples miss a sink that special-cases @Secret and forgets @Internal. The
/// lattice says @Internal cannot flow to @Public either, so this MUST also be rejected.
#[test]
fn spawn_internal_cap_into_public_init_is_rejected() {
    assert_spawn_leak_rejected(
        "spawn_internal.sigil",
        r#"module sigil;
cap type Fuel {}
actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}
entry actor Main {
    on Leak(f: Fuel @Internal) -> i64 {
        let w = spawn::<Worker>(f);
        return 0;
    }
}
"#,
        "@Internal cannot flow to @Public — a fix that only guards @Secret leaves this open",
    );
}

/// Positional zip: only the SECOND arg is tainted, into a @Public second init param. Guards against
/// a fix that checks only `args[0]`.
#[test]
fn spawn_second_arg_secret_is_rejected() {
    assert_spawn_leak_rejected(
        "spawn_second.sigil",
        r#"module sigil;
cap type Fuel {}
cap type Key {}
actor Worker {
    init(a: Fuel, b: Key) {}
    on Ping() -> i64 { return 0; }
}
entry actor Main {
    on Leak(a: Fuel, b: Key @Secret) -> i64 {
        let w = spawn::<Worker>(a, b);
        return 0;
    }
}
"#,
        "the second spawn arg is @Secret into a @Public init param — a first-arg-only check misses it",
    );
}

/// `@SecretCT` across the actor boundary is rejected wholesale (T028 / CT014), exactly as `send`/`ask`
/// reject it — inter-actor constant-time analysis is an anti-goal. Pinned on the T028 code because
/// this is the CT boundary, a distinct sink from the T001 flow check.
#[test]
fn spawn_secretct_cap_is_rejected_t028() {
    let source = r#"module sigil;
cap type Fuel {}
actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}
entry actor Main {
    on Leak(f: Fuel @SecretCT) -> i64 {
        let w = spawn::<Worker>(f);
        return 0;
    }
}
"#;
    match compile_named_module("spawn_ct.sigil", source) {
        Ok(_) => panic!("SOUNDNESS HOLE: a @SecretCT cap crossed the spawn boundary\n{source}"),
        Err(e) => {
            let d = err_debug(&e);
            assert!(
                d.contains("T028"),
                "a @SecretCT spawn payload must be rejected at the actor boundary (T028).\ngot: {d}"
            );
        }
    }
}

// ── Controls: safe spawns must still COMPILE (guard against "reject everything") ──────────────────

/// A @Secret cap into a @Secret-declared init param is sound (secret flows to secret) and MUST still
/// compile. Guards against a fix that over-taints and rejects safe programs.
#[test]
fn spawn_secret_cap_into_secret_init_compiles() {
    assert_compiles(
        "spawn_secret_ok.sigil",
        r#"module sigil;
cap type Fuel {}
actor Worker {
    init(f: Fuel @Secret) {}
    on Ping() -> i64 { return 0; }
}
entry actor Main {
    on Leak(f: Fuel @Secret) -> i64 {
        let w = spawn::<Worker>(f);
        return 0;
    }
}
"#,
        "a @Secret cap into a @Secret init param is sound and must compile",
    );
}

/// A @Public cap into a @Public init param — no taint anywhere — must compile.
#[test]
fn spawn_public_cap_into_public_init_compiles() {
    assert_compiles(
        "spawn_public_ok.sigil",
        r#"module sigil;
cap type Fuel {}
actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}
entry actor Main {
    on Leak(f: Fuel) -> i64 {
        let w = spawn::<Worker>(f);
        return 0;
    }
}
"#,
        "a spawn with no taint anywhere must compile after the spawn-sink fix",
    );
}

// ── Property-based: the spawn sink accepts IFF the arg taint can flow to the init param ───────────
//
// For arg taint `a` and declared init-param taint `b` drawn from the (non-CT) taint lattice
// {Public=0, Internal=1, Secret=2}, `spawn::<Worker>(<a-tagged cap>)` into `init(f: Fuel <b>)` must
// be ACCEPTED iff `a.can_flow_to(b)`, i.e. `a <= b`. This quantifies over the lattice rather than
// checking one point: it fails both for UNDER-tainting (the #253 bug: every (a>b) wrongly accepted)
// and for OVER-tainting (a fix that rejects a sound (a<=b) spawn).
mod props {
    use super::*;
    use proptest::prelude::*;

    /// Taint annotation for level `k` on a cap-typed param (0=Public → none, 1=Internal, 2=Secret).
    fn ann(k: usize) -> &'static str {
        match k {
            0 => "",
            1 => "@Internal",
            _ => "@Secret",
        }
    }

    proptest! {
        #[test]
        fn spawn_sink_accepts_iff_can_flow(a in 0usize..3, b in 0usize..3) {
            let source = format!(
                "module sigil;
                 cap type Fuel {{}}
                 actor Worker {{
                     init(f: Fuel {}) {{}}
                     on Ping() -> i64 {{ return 0; }}
                 }}
                 entry actor Main {{
                     on Leak(f: Fuel {}) -> i64 {{
                         let w = spawn::<Worker>(f);
                         return 0;
                     }}
                 }}
",
                ann(b), ann(a)
            );
            let compiles = compile_named_module("spawn_prop.sigil", &source).is_ok();
            // can_flow_to is `a <= b` on the lattice index.
            prop_assert_eq!(
                compiles, a <= b,
                "spawn sink must accept iff arg taint can flow to init param: a={} b={}", a, b
            );
        }
    }
}
