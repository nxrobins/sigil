//! AGG2b-4 — the two REAL holes the post-un-fence adversarial sweep found in the `mut Vec<scalar>`
//! state surface, now closed FAIL-CLOSED, plus the regression guards proving the fences do not
//! over-reject the intended direct-grow path, plus the documented false-alarm soundness. The
//! persistence payoff (a grown state Vec reads back
//! correctly across dispatches) lives in `sigil-runtime/tests/agg2b_state_vec_{persists,capstone}.rs`.
use sigil_compiler::compile_module;

fn codes(src: &str) -> Vec<String> {
    match compile_module(src) {
        Ok(_) => vec!["OK_CLEAN".to_string()],
        Err(e) => e
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

fn is_clean(src: &str) -> bool {
    compile_module(src).is_ok()
}

const HEAD: &str = "module sigil;\ncap type Fuel {}\n\
entry actor Main { state { fuel: Fuel } on Start() -> i64 { let w = spawn::<Acc>(fuel); return 0; } }\n";

// ── HOLE-TAINT — a bare `v.push(@Secret);` launders ─────────────────────────────────────────────

/// TVEC-01: the bug the AGG2b-3 regression missed by accidentally using the `let`-bound form. A BARE
/// `v.push(s);` expression statement (whose value taint is otherwise discarded) pushes a `@Secret`
/// element into a `@Public` state Vec, read back clean. The AGG2b-4 Call-arm sink now rejects it.
#[test]
fn bare_push_of_secret_into_state_vec_is_a_taint_launder() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Set(s: i64 @Secret) {{ v.push(s); }}\n\
         on Leak() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T001".to_string()),
        "a BARE `v.push(@Secret);` must be a T001 launder, not just the let-bound form; got {:?}",
        codes(&src)
    );
}

/// TVEC-06: the full cross-actor exfiltration arc — `@Secret` pushed into the state Vec, read back,
/// then `dest.send(Recv(out))` to a `@Public` handler. The push sink rejects it at the source.
#[test]
fn cross_actor_exfil_of_a_pushed_secret_is_blocked() {
    let src = "module sigil;
cap type Fuel {}
actor Sink { state { mut seen: i64 } init(f: Fuel) { seen = 0; } on Recv(p: i64) { seen = p; } }
entry actor Main { state { fuel: Fuel } on Start() -> i64 { let w = spawn::<Acc>(fuel); return 0; } }
actor Acc {
  state { mut v: Vec<i64> }
  init(f: Fuel) { let tmp: Vec<i64> = Vec::new(); v = tmp; }
  on Set(s: i64 @Secret) { v.push(s); }
  on Leak(dest: ActorRef<Sink>) { let out: i64 = v.get(0); dest.send(Recv(out)); }
}
";
    assert!(
        codes(src).contains(&"T001".to_string()),
        "pushing @Secret then exfiltrating must be blocked (T001 at the push); got {:?}",
        codes(src)
    );
}

/// The sink must not over-reject: a `@Public` value pushed into a `@Public` state Vec stays clean.
#[test]
fn pushing_public_into_state_vec_stays_clean() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Add(x: i64) {{ v.push(x); }}\n\
         on Get() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        is_clean(&src),
        "pushing a @Public value into a @Public state Vec must stay clean; got {:?}",
        codes(&src)
    );
}

// ── HOLE-DANGLE — an aliased grow bypasses the `$state` routing ──────────────────────────────────

/// AM-1: `let e = v; e.push(x)` roots the push receiver at the LOCAL `e`, so the AGG2b-2 `$state`
/// routing (keyed on a StateField root) MISSES it — the grow reallocs `v`'s buffer into the
/// transient arena and the AL-2 reset then reclaims it → the state Vec dangles. Fail-closed: the
/// alias is marked readonly, so the `@Mut` `push` is rejected by the T253 receiver gate.
#[test]
fn aliased_grow_of_a_state_vec_is_rejected() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Push(x: i64) {{ let e = v; let n: i64 = e.push(x); }}\n\
         on Get() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "growing a state Vec through an alias must be rejected (T253); got {:?}",
        codes(&src)
    );
}

/// AM-5: the transitive alias — `let e = v; let f = e; f.push(x)`. The readonly PROPAGATION carries
/// the mark from `e` to `f`, so the deeper alias is rejected too (no 1-hop escape).
#[test]
fn transitively_aliased_grow_of_a_state_vec_is_rejected() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Push(x: i64) {{ let e = v; let g = e; let n: i64 = g.push(x); }}\n\
         on Get() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        codes(&src).contains(&"T253".to_string()),
        "a transitively-aliased state-Vec grow must be rejected (T253); got {:?}",
        codes(&src)
    );
}

/// The fence must not over-reject the intended path: growing the state Vec DIRECTLY (`v.push(x)`,
/// which routes to `$state`) stays clean — the fence marks only LOCAL aliases, never the field.
#[test]
fn direct_grow_of_a_state_vec_stays_clean() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Push(x: i64) {{ let n: i64 = v.push(x); }}\n\
         on Get() -> i64 {{ return v.get(0); }}\n\
         }}\n"
    );
    assert!(
        is_clean(&src),
        "the DIRECT `v.push(x)` grow must stay clean (fence marks only aliases); got {:?}",
        codes(&src)
    );
}

/// Reading through an alias stays legal: `v.get` is `@ReadOnly self`, so the T253 receiver gate does
/// not fire on a frozen alias — only the `@Mut` grow does.
#[test]
fn reading_a_state_vec_through_an_alias_stays_clean() {
    let src = format!(
        "{HEAD}actor Acc {{\n\
         state {{ mut v: Vec<i64> }}\n\
         init(f: Fuel) {{ let tmp: Vec<i64> = Vec::new(); v = tmp; }}\n\
         on Add(x: i64) {{ let n: i64 = v.push(x); }}\n\
         on Get() -> i64 {{ let e = v; return e.get(0); }}\n\
         }}\n"
    );
    assert!(
        is_clean(&src),
        "reading a state Vec through an alias (@ReadOnly self) must stay clean; got {:?}",
        codes(&src)
    );
}

// ── Documented false alarms — the sweep flagged these but each is a SOUND fail-closed trap ───────

/// AM-2: passing a `mut` state Vec to a MUTATING free fn is T253 (the param is a frozen `Default`
/// receiver, so `xs.push` is a frozen-receiver mutation) — the AGG-4 fence already holds here.
#[test]
fn passing_state_vec_to_a_mutating_free_fn_is_rejected() {
    let src = "module sigil;
cap type Fuel {}
fn grow_it(xs: Vec<i64>, x: i64) -> i64 { return xs.push(x); }
entry actor Main { state { fuel: Fuel } on Start() -> i64 { let w = spawn::<Acc>(fuel); return 0; } }
actor Acc {
  state { mut v: Vec<i64> }
  init(f: Fuel) { let tmp: Vec<i64> = Vec::new(); v = tmp; }
  on Push(x: i64) { let n: i64 = grow_it(v, x); }
  on Get() -> i64 { return v.get(0); }
}
";
    assert!(
        codes(src).contains(&"T253".to_string()),
        "passing a state Vec to a mutating free fn must be rejected (T253); got {:?}",
        codes(src)
    );
}

/// AM-6 (found by the AGG2b-4 re-sweep, NOT in the original fixture set): a `mut` state Vec passed
/// to a `@Mut Vec` param is NOT frozen, so the AGG-4 gate lets it through — but the callee's
/// `xs.push` roots at its own param, mis-routing the realloc into transient memory → dangle. The
/// AGG2b-4 free-call gate rejects it fail-closed (the callee could grow it; we cannot prove it won't).
#[test]
fn passing_state_vec_to_a_mut_param_that_could_grow_is_rejected() {
    let src = "module sigil;
cap type Fuel {}
fn grow(xs: Vec<i64> @Mut, x: i64) -> i64 { return xs.push(x); }
entry actor Main { state { fuel: Fuel } on Start() -> i64 { let w = spawn::<Acc>(fuel); return 0; } }
actor Acc {
  state { mut v: Vec<i64> }
  init(f: Fuel) { let tmp: Vec<i64> = Vec::new(); v = tmp; }
  on Push(x: i64) { let n: i64 = grow(v, x); }
  on Get() -> i64 { return v.get(0); }
}
";
    assert!(
        codes(src).contains(&"T253".to_string()),
        "passing a state Vec to a @Mut Vec param (the callee could grow it) must be rejected \
         (T253); got {:?}",
        codes(src)
    );
}

/// fe-*: AGG-2b's un-fence admitted only `Vec<scalar>`; PPS-3 widened it to FLAT record
/// elements (the storing push copies the registry-listed fields into persistent memory). The
/// element cells still hold heap pointers — but pointers to PROMOTED copies now. The line
/// moved to pointer-bearing element INTERIORS, fenced in `pps3_record_element_fences.rs`.
#[test]
fn vec_of_record_state_field_is_admitted_since_pps3() {
    let src = format!(
        "{HEAD}record Pt {{ x: i64, y: i64 }}\n\
         actor Acc {{\n\
         state {{ mut v: Vec<Pt> }}\n\
         init(f: Fuel) {{ let tmp: Vec<Pt> = Vec::new(); v = tmp; }}\n\
         on Ping() -> i64 {{ return 0; }}\n\
         }}\n"
    );
    assert!(
        !codes(&src).contains(&"C012".to_string()),
        "PPS-3 admits `mut Vec<Pt>` state; got {:?}",
        codes(&src)
    );
}
