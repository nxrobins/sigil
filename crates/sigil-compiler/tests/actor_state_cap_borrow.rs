//! M4 — borrow-only state capabilities (C010).
//!
//! A capability HELD in actor state is *borrow-only* inside an ordinary message
//! handler: non-consuming uses (`grant(&f, …)`, `f.draw(n)`) are allowed, but any
//! CONSUME — spawn arg, send/ask payload, `.split`, `.restrict`, move-by-value,
//! record/tuple field move, return — is rejected with **C010**. Consuming is
//! permitted ONLY during the construction phase (`init`, or the entry actor's
//! `Start` boot handler), which runs once before the confluent steady state.
//!
//! This suite is the SC-1 "borrow-only is unlaunderable" gate: the `StateCap`
//! marker MUST propagate through every binding / aggregate / escape channel, so a
//! consume of any state-cap-DERIVED value in a handler is still C010. Each
//! laundering channel below (`let`-alias, message payload, record field,
//! call-by-value, return) must independently fire C010; if any stops firing, a
//! laundering hole has opened and this test goes red.

use sigil_compiler::compile_named_module;
use sigil_compiler::diagnostics::Severity;

/// Compile `src` and return every `Error`-severity code it emits.
fn error_codes(name: &str, src: &str) -> Vec<String> {
    match compile_named_module(name, src) {
        Ok(_) => Vec::new(),
        Err(e) => e
            .diagnostics()
            .iter()
            .filter(|d| d.severity() == Severity::Error)
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn fires_c010(name: &str, src: &str) -> bool {
    error_codes(name, src).iter().any(|c| c == "C010")
}

fn fires_t127(name: &str, src: &str) -> bool {
    error_codes(name, src).iter().any(|c| c == "T127")
}

fn compiles_clean(name: &str, src: &str) -> bool {
    error_codes(name, src).is_empty()
}

/// Preamble: a `Worker` actor (init + a `Take(Fuel)` message + `Ping`), plus the
/// `Fuel` cap type. The entry actor's body is spliced into `{BODY}` /`{RET}` of a
/// `Tick` handler (an ORDINARY handler — not `Start` — so consuming state is C010).
fn handler_module(body: &str) -> String {
    handler_module_ret("i64", body, "return 1;")
}

fn handler_module_ret(ret: &str, body: &str, ret_stmt: &str) -> String {
    format!(
        "module sigil;
cap type Fuel {{}}

actor Worker {{
    init(f: Fuel) {{}}
    on Take(f: Fuel) -> i64 {{ return 0; }}
    on Ping() -> i64 {{ return 0; }}
}}

entry actor Main {{
    state {{ fuel: Fuel }}

    on Start() -> i64 {{ return 0; }}

    on Tick(wref: ActorRef<Worker>) -> {ret} {{
        {body}
        {ret_stmt}
    }}
}}
"
    )
}

// ── Negative: every consume channel in an ordinary handler → C010 ────────────

#[test]
fn handler_direct_spawn_of_state_cap_is_c010() {
    let src = handler_module("let w = spawn::<Worker>(fuel);");
    assert!(
        fires_c010("direct_spawn", &src),
        "spawning with a state cap in a handler must be C010; got {:?}",
        error_codes("direct_spawn", &src)
    );
}

#[test]
fn handler_let_alias_launder_is_c010() {
    // SC-1: `let x = fuel` borrow-aliases the marker; the later consume of `x`
    // must still be C010 (the marker propagated through the `let`).
    let src = handler_module("let x = fuel;\n        let w = spawn::<Worker>(x);");
    assert!(
        fires_c010("let_alias", &src),
        "let-aliased state cap consume must be C010; got {:?}",
        error_codes("let_alias", &src)
    );
}

#[test]
fn handler_message_payload_launder_is_c010() {
    // The send payload `Take(fuel)` lowers to a RecordConstruct that MOVES fuel
    // into the message — a consume of state → C010 (the F007-adjacent boundary).
    let src = handler_module("wref.send(Take(fuel));");
    assert!(
        fires_c010("send_payload", &src),
        "state cap in a send payload must be C010; got {:?}",
        error_codes("send_payload", &src)
    );
}

#[test]
fn handler_split_of_state_cap_is_c010() {
    let src = handler_module("let w = spawn::<Worker>(fuel.split(1));");
    assert!(
        fires_c010("split", &src),
        "`.split` consumes the parent — on a state cap in a handler that is C010; got {:?}",
        error_codes("split", &src)
    );
}

#[test]
fn handler_return_of_state_cap_is_c010() {
    // Returning the cap moves it across the actor boundary — a consume.
    let src = handler_module_ret("Fuel", "", "return fuel;");
    assert!(
        fires_c010("return_state_cap", &src),
        "returning a state cap from a handler must be C010; got {:?}",
        error_codes("return_state_cap", &src)
    );
}

#[test]
fn handler_return_after_alias_is_c010() {
    // return-then-reuse style: alias, then return the alias.
    let src = handler_module_ret("Fuel", "let x = fuel;", "return x;");
    assert!(
        fires_c010("return_alias", &src),
        "returning a let-aliased state cap must be C010; got {:?}",
        error_codes("return_alias", &src)
    );
}

#[test]
fn handler_call_by_value_launder_is_c010() {
    // Passing a state cap by value to a free function is a move → consume → C010.
    let src = "module sigil;
cap type Fuel {}

fn eat(f: Fuel) -> i64 { return 0; }

actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 0; }
    on Tick() -> i64 {
        let r = eat(fuel);
        return r;
    }
}
";
    assert!(
        fires_c010("call_by_value", src),
        "passing a state cap by value to a fn must be C010; got {:?}",
        error_codes("call_by_value", src)
    );
}

#[test]
fn handler_tuple_construct_launder_is_c010() {
    // SC-1 aggregate channel: moving a state cap INTO a tuple is a consume — the
    // `RecordConstruct` arm fires C010 at construction (before any extraction, so
    // the un-parseable `t.0` element access never even matters).
    let src = handler_module("let t = (fuel, 0);");
    assert!(
        fires_c010("tuple_construct", &src),
        "moving a state cap into a tuple must be C010; got {:?}",
        error_codes("tuple_construct", &src)
    );
}

#[test]
fn handler_return_tuple_with_state_cap_is_c010() {
    // Returning a tuple that carries the state cap moves it across the actor
    // boundary — a consume — so C010 fires on the tuple construction.
    let src = "module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 0; }
    on Tick() -> (Fuel, i64) { return (fuel, 0); }
}
";
    assert!(
        fires_c010("return_tuple", src),
        "returning a tuple carrying a state cap must be C010; got {:?}",
        error_codes("return_tuple", src)
    );
}

// NOTE — two SC-1 aggregate channels are closed UPSTREAM of C010, which is a
// strictly stronger guarantee (the state cap never reaches an AIR consume site):
//   * user-declared records: `record W { f: Fuel }` is rejected at declaration by
//     T183 (caps may not be record fields), so a state cap can never be laundered
//     through a record literal. The ONLY cap-bearing `RecordConstruct` is the
//     synthetic message payload — covered by `handler_message_payload_launder`.
//   * `match`-expression yielding a bare cap is not a SIGIL surface idiom (arms
//     are statement bodies); any value-yielding bind routes through the same
//     `Assign{Var}` borrow-alias channel as `let` — covered by the `let`-alias and
//     return-after-alias cases above.

// ── Positive: borrows in a handler, and consumes during construction ─────────

#[test]
fn handler_draw_of_state_cap_is_allowed() {
    // `.draw(n)` is use-not-move — a borrow. Borrow-only permits it in a handler.
    let src = handler_module("let w = spawn::<Worker>(fuel.draw(1));");
    assert!(
        !fires_c010("draw", &src),
        "`.draw` is a borrow and must NOT be C010 in a handler; got {:?}",
        error_codes("draw", &src)
    );
}

#[test]
fn entry_start_may_consume_state_cap() {
    // The boot carve-out: the entry actor's `Start` handler runs once at
    // construction and MAY consume state (root→child authority delegation).
    let src = "module sigil;
cap type Fuel {}

actor Worker {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let w = spawn::<Worker>(fuel);
        return 0;
    }
}
";
    assert!(
        !fires_c010("entry_start_consume", src),
        "consuming state fuel in the entry `Start` boot handler must be allowed; got {:?}",
        error_codes("entry_start_consume", src)
    );
}

#[test]
fn spawned_actor_init_may_consume_state_cap() {
    // The other half of the carve-out: `init` is construction, so an `init` that
    // stores a cap into state and then consumes it during construction is allowed.
    let src = "module sigil;
cap type Fuel {}

actor Grandchild {
    init(f: Fuel) {}
    on Ping() -> i64 { return 0; }
}

actor Parent {
    state { power: Fuel }
    init(x: Fuel) {
        power = x;
        let g = spawn::<Grandchild>(power);
    }
    on Ping() -> i64 { return 0; }
}

entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 {
        let p = spawn::<Parent>(fuel);
        return 0;
    }
}
";
    assert!(
        !fires_c010("init_consume", src),
        "consuming a just-assigned state cap during `init` must be allowed; got {:?}",
        error_codes("init_consume", src)
    );
}

// ── Closure / grant capture launder (adversarial hunt, SC-1 crux) ────────────
//
// The `StateCap` marker only propagates through the `Assign{Var}` borrow-alias
// arm; a closure capture lowers to a raw `StoreField` into the closure env, which
// (before the fix) `apply_moves` ignored — so a state cap captured into a closure
// and consumed inside its body escaped C010. `grant` is the sanctioned dispatch
// that actually INVOKES such a closure (general indirect call of a cap-capturing
// linear closure is blocked by T237). Two-layer defense: T127 rejects capturing a
// state field BY NAME at type-check (also prevents the `lower_state_read` ICE);
// the ownership `StoreField` arm fires C010 when a state-cap ALIAS var is captured.

const WORKER: &str = "cap type Fuel {}
actor Worker {
    init(f: Fuel) {}
    on Take(f: Fuel) -> i64 { return 0; }
    on Ping() -> i64 { return 0; }
}
";

#[test]
fn closure_captures_state_field_by_name_is_t127() {
    // Direct capture of the state field `fuel` — rejected at type-check (T127),
    // which also prevents the closure-body state-read ICE.
    let src = format!(
        "module sigil;
{WORKER}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{ return 0; }}
    on Tick() -> i64 {{
        let leak = fn() -> i64 {{ let w = spawn::<Worker>(fuel); return 0; }};
        return 0;
    }}
}}
"
    );
    assert!(
        fires_t127("closure_direct_name", &src),
        "capturing a state field by name must be T127; got {:?}",
        error_codes("closure_direct_name", &src)
    );
    // Never an ICE / panic (compile returns cleanly-typed diagnostics).
    assert!(
        !error_codes("closure_direct_name", &src).is_empty(),
        "must be rejected, not compile clean"
    );
}

#[test]
fn grant_closure_captures_state_alias_is_c010() {
    // The headline hunt exploit: alias the state cap to a local, capture the ALIAS
    // in a grant closure, consume it inside the body. The alias `g` is in the
    // ownership state_cap set (Assign{Var} propagation); the capture StoreField now
    // fires C010.
    let src = format!(
        "module sigil;
{WORKER}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{ return 0; }}
    on Tick() -> i64 {{
        let g = fuel;
        grant(&g, fn(r: &Fuel) -> i64 {{ let w = spawn::<Worker>(g); return 0; }});
        return 1;
    }}
}}
"
    );
    assert!(
        fires_c010("grant_capture_alias", &src),
        "capturing a state-cap alias into a grant closure must be C010; got {:?}",
        error_codes("grant_capture_alias", &src)
    );
}

#[test]
fn grant_decoy_cap_closure_captures_state_alias_is_c010() {
    // grant borrows an unrelated param cap; the closure body consumes the captured
    // state alias. Proves the launder is independent of what grant grants.
    let src = format!(
        "module sigil;
{WORKER}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{ return 0; }}
    on Tick(other: Fuel) -> i64 {{
        let g = fuel;
        grant(&other, fn(r: &Fuel) -> i64 {{ let w = spawn::<Worker>(g); return 0; }});
        return 1;
    }}
}}
"
    );
    assert!(
        fires_c010("grant_decoy_alias", &src),
        "state-cap alias captured while granting a decoy cap must be C010; got {:?}",
        error_codes("grant_decoy_alias", &src)
    );
}

#[test]
fn closure_captures_state_alias_even_if_never_invoked_is_c010() {
    // Capturing the state-cap alias is itself the violation — no invocation needed.
    let src = format!(
        "module sigil;
{WORKER}
entry actor Main {{
    state {{ fuel: Fuel }}
    on Start() -> i64 {{ return 0; }}
    on Tick() -> i64 {{
        let g = fuel;
        let mk = fn() -> i64 {{ let w = spawn::<Worker>(g); return 0; }};
        return 1;
    }}
}}
"
    );
    assert!(
        fires_c010("capture_never_invoked", &src),
        "capturing a state-cap alias into a closure must be C010 even if never called; got {:?}",
        error_codes("capture_never_invoked", &src)
    );
}

#[test]
fn grant_borrow_of_state_cap_is_allowed() {
    // The SANCTIONED borrow: grant passes `&fuel`; the closure receives a `&Fuel`
    // PARAMETER (`r`) and uses it non-consumingly. `fuel` is the grant argument
    // (evaluated in the handler), NOT a free variable of the closure body, so it is
    // not captured — clean.
    let src = "module sigil;
cap type Fuel {}
fn peek(r: &Fuel) -> i64 { return 0; }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 0; }
    on Tick() -> i64 {
        return grant(&fuel, fn(r: &Fuel) -> i64 { return peek(r); });
    }
}
";
    assert!(
        compiles_clean("grant_borrow", src),
        "grant-borrowing a state cap (closure uses the &Fuel param) must compile clean; got {:?}",
        error_codes("grant_borrow", src)
    );
}

#[test]
fn draw_shard_send_is_allowed() {
    // `.draw(n)` sub-divides Fuel: the parent stays in state (borrow preserved), a
    // BOUNDED shard is produced as a fresh owned cap. Delegating that shard (here
    // via a send) is the sanctioned, quantity-conserving delegation — not a launder.
    let src = "module sigil;
cap type Fuel {}
actor Worker { init(f: Fuel) {} on Take(f: Fuel) -> i64 { return 0; } }
entry actor Main {
    state { fuel: Fuel }
    on Start() -> i64 { return 0; }
    on Tick(wref: ActorRef<Worker>) -> i64 {
        let shard = fuel.draw(1);
        wref.send(Take(shard));
        return 1;
    }
}
";
    assert!(
        compiles_clean("draw_send", src),
        "sending a drawn Fuel shard must compile clean (sanctioned sub-division); got {:?}",
        error_codes("draw_send", src)
    );
}

// SCOPE BOUNDARY (documented, tested elsewhere): C010 governs BARE `cap`-typed
// state fields (immutable, borrow-only). It deliberately does NOT cover:
//   * `Slot<Cap>` state fields — an EXPLICIT interior-mutability mechanism whose
//     linearity routes through the dedicated SlotPut/SlotTake AIR ops + runtime
//     empty-slot trap (see validators.rs `Slot` reserved-name note). Handler-time
//     `slot_take` is the CORE of the tested quorum pattern (z3_corpus/17,18), so it
//     is intended, not a launder; an actor using `Slot<Cap>` opts out of the
//     immutable-state confluence property by construction.
//   * `.draw(n)` shards — a bounded, quantity-conserving sub-division of divisible
//     Fuel (see `draw_shard_send_is_allowed` above and z3_corpus/09).

// ── Guard: a NON-state linear cap (handler param) keeps ordinary O001 ─────────

#[test]
fn handler_param_cap_double_use_is_o001_not_c010() {
    // A cap that FLOWS IN as a message payload is an ordinary linear local, not a
    // state cap: using it twice is O001 (use-after-move), never C010.
    let src = "module sigil;
cap type Fuel {}

actor Worker {
    init(f: Fuel) {}
    on Take(f: Fuel) -> i64 { return 0; }
}

entry actor Main {
    on Tick(wref: ActorRef<Worker>, f: Fuel) -> i64 {
        wref.send(Take(f));
        wref.send(Take(f));
        return 1;
    }
}
";
    let codes = error_codes("param_double_use", src);
    assert!(
        codes.iter().any(|c| c == "O001"),
        "double-use of a flowing param cap must be O001; got {codes:?}"
    );
    assert!(
        !codes.iter().any(|c| c == "C010"),
        "a flowing param cap is not state — must NOT be C010; got {codes:?}"
    );
}
