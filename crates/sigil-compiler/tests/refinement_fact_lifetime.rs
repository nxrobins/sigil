//! A refinement fact dies with the binding it describes (the design-by-contract spec's DBC-0a):
//! a refined call whose argument has no fact is refused (T211); a `mut` binding carries no fact,
//! so a narrowing on it records nothing and a `let mut` of a refined value keeps nothing; and a
//! fresh binding shadows an outer name's facts, a refined parameter's included. Each test pairs
//! the once-accepted form with its twin, the same shape with no stale fact, and requires the same
//! exact refusal of both in this build's configuration (the collector's T211 runs with and
//! without the solver): the twin shows the checker sees the shape, the other form that no fact
//! reaches the call any more. The forms are the spec's probes P4, P8, P10, P12 and P13 (draft
//! PR 761, section 3.1), accepted and certified until DBC-0a. The `match`-binding and
//! closure-parameter shadowing forms live in the runtime crate's `instance_body_context` suite.
//!
//! A field store is a refinement sink (DBC-0b, the spec's DBC0-3, probe P11): a store into a
//! refined record's field gets the construction site's dispatch, keyed on the place's record
//! type. The store tests below pin each form the way its obligation is decided: by the solver
//! where a construction site's literal is (refused with the solver, collected and not decided
//! without it: SR-038), and in both builds where the collector refuses on its own.
//!
//! The second DBC-0a review found three binding sites short of the rules: a tuple `let`, whose
//! desugar wrote its entries into a frame the nested block popped; a `match` binding, an iterator
//! loop variable and a plain `let` that reuse the name of an outer `let mut`, which T042's by-name
//! mutable set still lets the scope assign while their entries said immutable; and an actor state
//! field the body may write, which no entry describes. Each is pinned below the same way.

use std::collections::BTreeSet;

use sigil_test_utils::pipeline::{compile_module_codes, compile_tool_codes};

/// An iterator (`for x in make_counter(n)` runs `x` over `0..n`), for the loop-variable forms.
const COUNTER: &str = "record Counter { cur: i64, max: i64 }\nimpl Counter {\n    pub fn next(self: \
                       Counter @Mut) -> Option<i64> { if self.cur < self.max { let v: i64 = \
                       self.cur; self.cur = self.cur + 1; return Some(v); } else { return None; } \
                       }\n}\nfn make_counter(n: i64) -> Counter { return Counter { cur: 0, max: n \
                       }; }\n";

/// A tool with `need_positive` and `extra` declared, whose entry binds the untrusted `input` and
/// runs `body`.
fn tool(extra: &str, body: &str) -> String {
    format!(
        "module tool;\nfn need_positive(x: i64) where x > 0 -> i64 {{\n    return x;\n}}\n{extra}\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n    \
         let input: i64 = input_len;\n    {body}\n}}\n"
    )
}

fn codes(source: &str) -> BTreeSet<String> {
    compile_tool_codes(source).into_iter().collect()
}

/// `stale` (the form a stale fact once discharged) and `twin` (the same shape with no fact at
/// all) are both refused with exactly T211.
fn assert_refused_alike(form: &str, stale: &str, twin: &str) {
    let want = BTreeSet::from(["T211".to_string()]);
    assert_eq!(
        codes(twin),
        want,
        "{form}: the twin without a fact must be refused with T211, or the other form proves nothing"
    );
    assert_eq!(
        codes(stale),
        want,
        "{form}: a fact reached the call past the binding that ended it (DBC-0a regressed)"
    );
}

/// The records and callees of the field-store tests: `Index` and `Range` carry a clause, `Plain`
/// and `Span` are their clause-free twins, `Outer`/`OuterP` nest them, `big` returns a value
/// with a fact.
const STORE_DECLS: &str = "record Index { value: i64 } where value > 100\n\
record Plain { value: i64 }\n\
record Outer { inner: Index }\n\
record OuterP { inner: Plain }\n\
record Range { lo: i64, hi: i64 } where lo <= hi\n\
record Span { lo: i64, hi: i64 }\n\
fn need_big(x: i64) where x > 100 -> i64 {\n    return x;\n}\n\
fn big() -> i64 where @ > 100 {\n    return 500;\n}\n";

/// The `@Mut`-parameter callees, declared only by the row that calls them: each stores into its
/// parameter's field and reads it back through `need_big`, so a program that declares one carries
/// that store's verdict.
const CLOBBER: &str =
    "fn clobber(i: Index @Mut) -> i64 {\n    i.value = 5;\n    return need_big(i.value);\n}\n";
const CLOBBER_PLAIN: &str = "fn clobber_plain(p: Plain @Mut) -> i64 {\n    p.value = 5;\n    return need_big(p.value);\n}\n";

/// A store whose obligation is the solver's to decide, as a construction site's literal is: with
/// the solver, `stale` (the store that breaks the record's invariant, then a read that takes the
/// invariant as its fact) is refused with exactly `code`; without it the obligation is collected
/// and not decided (SR-038), so the program compiles and its certificate says
/// `solver_verified: false`. `twin`, the same shape with no clause to break, is refused with
/// exactly T211 in both builds: the read's fact, which the sink now vouches for, is what it lacks.
fn assert_store_decided_by_the_solver(form: &str, stale: &str, twin: &str, code: &str) {
    assert_eq!(
        codes(twin),
        BTreeSet::from(["T211".to_string()]),
        "{form}: the twin without a clause must be refused with T211, or the other form proves \
         nothing"
    );
    if cfg!(feature = "solver") {
        assert_eq!(
            codes(stale),
            BTreeSet::from([code.to_string()]),
            "{form}: a store that breaks the record's invariant was not refused at the store \
             (DBC-0b regressed)"
        );
    } else {
        let compiled = sigil_compiler::compile_tool(stale).unwrap_or_else(|_| {
            panic!(
                "{form}: refused with {:?} in a build that cannot decide the obligation: either \
                 the collector now refuses the form on its own, or this build decides it (SR-038 \
                 moved); update the test and SR-038",
                codes(stale)
            )
        });
        assert!(
            !compiled.solver_verified,
            "{form}: accepted without the solver, yet certified solver-verified"
        );
    }
}

/// A store refused in both builds, with exactly `code`, beside `kept`, the same shape whose store
/// keeps the invariant, accepted in both: the refusal is the store's, not the shape's.
fn assert_store_refused_in_both_builds(form: &str, stale: &str, kept: &str, code: &str) {
    assert_eq!(
        codes(kept),
        BTreeSet::new(),
        "{form}: the store that keeps the invariant must be accepted, or the refusal is of the \
         shape, not the store"
    );
    assert_eq!(
        codes(stale),
        BTreeSet::from([code.to_string()]),
        "{form}: the store was not refused (DBC-0b regressed)"
    );
}

/// A `mut` binding carries no fact (DBC0-2): an `if` narrowing (`y > 0`), the same narrowing
/// across a loop back-edge, and a refined return (`pos() -> i64 where @ > 0`) each leave
/// `need_positive` undischarged after the variable is assigned 0, a decrement, or -3 — and
/// before it: the narrowing records nothing for a `mut` name, and `let mut p = pos()` keeps
/// nothing, so the call is refused whether or not the assignment follows.
#[test]
fn refinement_fact_dies_with_its_mutable_binding() {
    let pos = "fn pos() -> i64 where @ > 0 {\n    return 1;\n}\n";
    for (form, extra, stale, twin) in [
        (
            "narrowed, then assigned",
            "",
            "let mut y: i64 = input; if y > 0 { y = 0; return need_positive(y); } return 1;",
            "let mut y: i64 = input; y = 0; return need_positive(y);",
        ),
        (
            "narrowed, then decremented across a loop back-edge",
            "",
            "let mut y: i64 = input; let mut acc: i64 = 0; if y > 0 { while y > 0 - 5 { acc = acc + \
             need_positive(y); y = y - 1; } } return acc;",
            "let mut y: i64 = input; let mut acc: i64 = 0; while y > 0 - 5 { acc = acc + \
             need_positive(y); y = y - 1; } return acc;",
        ),
        (
            "refined return, then assigned",
            pos,
            "let mut p: i64 = pos(); p = 0 - 3; return need_positive(p);",
            "let mut p: i64 = input; p = 0 - 3; return need_positive(p);",
        ),
        (
            "tuple binding narrowed, then assigned",
            "",
            "let (mut y, z) = (input, input); if y > 0 { y = 0; return need_positive(y); } return 1;",
            "let (mut y, z) = (input, input); y = 0; return need_positive(y);",
        ),
    ] {
        assert_refused_alike(form, &tool(extra, stale), &tool(extra, twin));
    }
}

/// A binding that reuses a name the scope may still assign carries no fact (DBC0-2 at its root).
/// T042's mutable set is by name, so an immutable binding that shadows an outer `let mut` of its
/// name stays assignable: a `let` (bound to a refined return, or narrowed), a tuple binding, a
/// `match` binding (a variant payload, or a catch-all bound to a refined scrutinee) and an
/// iterator loop variable. Each form assigns to the inner binding, so the entry must be mutable
/// there: the narrowing records nothing and the value's fact is dropped. The twin is the same
/// shape with no fact to drop.
#[test]
fn a_binding_that_reuses_an_assignable_name_carries_no_fact() {
    let pos = "fn pos() -> i64 where @ > 0 {\n    return 1;\n}\n";
    for (form, extra, stale, twin) in [
        (
            "let of a refined return, shadowing a let mut",
            pos,
            "let mut x: i64 = input; if input > 0 { let x: i64 = pos(); x = 0; return \
             need_positive(x); } return 1;",
            "let mut x: i64 = input; if input > 0 { let x: i64 = input + 1; x = 0; return \
             need_positive(x); } return 1;",
        ),
        (
            "let narrowed, shadowing a let mut",
            "",
            "let mut x: i64 = input; if input > 0 { let x: i64 = input + 1; if x > 0 { x = 0; \
             return need_positive(x); } } return 1;",
            "let mut x: i64 = input; if input > 0 { let x: i64 = input + 1; x = 0; return \
             need_positive(x); } return 1;",
        ),
        (
            "tuple binding narrowed, shadowing a let mut",
            "",
            "let mut x: i64 = input; if input > 0 { let (x, z) = (input, input); if x > 0 { x = \
             0; return need_positive(x); } } return 1;",
            "let mut x: i64 = input; if input > 0 { let (x, z) = (input, input); x = 0; return \
             need_positive(x); } return 1;",
        ),
        (
            "match binding narrowed, shadowing a let mut",
            "",
            "let mut x: i64 = input; let o: Option<i64> = Some(input); match o { Some(x) => { if \
             x > 0 { x = 0; return need_positive(x); } return 1; }, None => { return 1; }, } \
             return 1;",
            "let mut x: i64 = input; let o: Option<i64> = Some(input); match o { Some(x) => { x \
             = 0; return need_positive(x); }, None => { return 1; }, } return 1;",
        ),
        (
            "catch-all match binding of a refined scrutinee, shadowing a let mut",
            pos,
            "let mut v: i64 = input; match pos() { v => { v = 0; return need_positive(v); }, } \
             return 1;",
            "let mut v: i64 = input; match input { v => { v = 0; return need_positive(v); }, } \
             return 1;",
        ),
        (
            "iterator loop variable narrowed, shadowing a let mut",
            COUNTER,
            "let mut x: i64 = input; for x in make_counter(3) { if x > 0 { x = 0; return \
             need_positive(x); } } return 1;",
            "let mut x: i64 = input; for x in make_counter(3) { x = 0; return need_positive(x); \
             } return 1;",
        ),
    ] {
        assert_refused_alike(form, &tool(extra, stale), &tool(extra, twin));
    }
}

/// The actor-module prelude for the state-field forms: `need_positive` declared, and an entry
/// actor that spawns `Acc`.
const ACTOR_HEAD: &str = "module sigil;\ncap type Fuel {}\nfn need_positive(x: i64) where x > 0 \
                          -> i64 {\n    return x;\n}\nentry actor Main { state { fuel: Fuel } on \
                          Start() -> i64 { let w = spawn::<Acc>(fuel); return 0; } }\n";

/// An `Acc` actor with the given `state` fields, `init` body and handler.
fn actor(state: &str, init: &str, handler: &str) -> String {
    format!(
        "{ACTOR_HEAD}actor Acc {{\n  state {{ {state} }}\n  init(f: Fuel) {{ {init} }}\n  {handler}\n}}\n"
    )
}

fn module_codes(source: &str) -> BTreeSet<String> {
    compile_module_codes(source).into_iter().collect()
}

/// An actor state field the body may write carries no fact (DBC0-2): a `mut` field in a handler,
/// and any field in `init`, the construction phase that writes every field. No entry describes a
/// state field (a binding cannot shadow one), so the narrowing rule decides by the field itself:
/// `if count > 0` records nothing for such a field, and `need_positive(count)` after `count = 0`
/// is refused, as the twin with no narrowing is. A field a handler cannot write keeps the
/// narrowing, so the rule refuses the assignable field, not the state read.
#[test]
fn an_assignable_state_field_carries_no_fact() {
    let want = BTreeSet::from(["T211".to_string()]);
    for (form, state, init, handler, twin_init, twin_handler) in [
        (
            "mut field narrowed, then assigned in a handler",
            "mut count: i64",
            "count = 5;",
            "on Tick() -> i64 { if count > 0 { count = 0; return need_positive(count); } return 1; }",
            "count = 5;",
            "on Tick() -> i64 { count = 0; return need_positive(count); }",
        ),
        (
            "field narrowed, then assigned in init",
            "count: i64",
            "count = 5; if count > 0 { count = 0; let n: i64 = need_positive(count); }",
            "on Tick() -> i64 { return 1; }",
            "count = 0; let n: i64 = need_positive(count);",
            "on Tick() -> i64 { return 1; }",
        ),
    ] {
        assert_eq!(
            module_codes(&actor(state, twin_init, twin_handler)),
            want,
            "{form}: the twin without a narrowing must be refused with T211, or the other form \
             proves nothing"
        );
        assert_eq!(
            module_codes(&actor(state, init, handler)),
            want,
            "{form}: a narrowing's fact survived an assignment to the state field (DBC-0a regressed)"
        );
    }
    assert_eq!(
        module_codes(&actor(
            "count: i64",
            "count = 5;",
            "on Tick() -> i64 { if count > 0 { return need_positive(count); } return 1; }",
        )),
        BTreeSet::new(),
        "a field no handler can write must keep its narrowing"
    );
}

/// The immutable counterpart, so the rule refuses the `mut` binding and not the narrowing: an
/// immutable `let` narrowed by `if y > 0` still discharges `need_positive(y)` inside the arm,
/// and `let p: i64 = pos()` still carries the refined return to the call.
#[test]
fn an_immutable_binding_keeps_its_fact() {
    let pos = "fn pos() -> i64 where @ > 0 {\n    return 1;\n}\n";
    for (form, extra, body) in [
        (
            "narrowed immutable let",
            "",
            "let y: i64 = input; if y > 0 { return need_positive(y); } return 1;",
        ),
        (
            "refined return bound immutably",
            pos,
            "let p: i64 = pos(); return need_positive(p);",
        ),
        (
            "narrowed immutable tuple binding",
            "",
            "let (y, z) = (input, input); if y > 0 { return need_positive(y); } return 1;",
        ),
        (
            "catch-all match binding of a refined scrutinee",
            pos,
            "match pos() { v => { return need_positive(v); }, } return 1;",
        ),
    ] {
        assert_eq!(
            codes(&tool(extra, body)),
            BTreeSet::new(),
            "{form}: an immutable binding's fact must still discharge the call"
        );
    }
}

/// A store into a refined record's field is a refinement sink (DBC0-3, probe P11): a literal
/// the clause refutes is a `LiteralFits` obligation at the store, refused with T210 where the
/// solver decides it, so a read of the field keeps taking its fact from the record type. The rule
/// is keyed on the place's record TYPE, not on how the place was reached: a local's field, a
/// nested field, an array element's field, a field reached through a `&mut` borrow and a store
/// through an `@Mut` parameter are one case. Each form beside its twin, the same shape on the
/// clause-free `Plain`, where the read has no fact and the call is refused with T211.
#[test]
fn a_field_store_is_a_refinement_sink() {
    for (form, stale_decls, stale, twin_decls, twin) in [
        (
            "literal store into a local's field (P11)",
            "",
            "let mut i: Index = Index { value: 200 }; i.value = 5; return need_big(i.value);",
            "",
            "let mut p: Plain = Plain { value: 200 }; p.value = 5; return need_big(p.value);",
        ),
        (
            "nested place",
            "",
            "let mut o: Outer = Outer { inner: Index { value: 200 } }; o.inner.value = 5; \
             return need_big(o.inner.value);",
            "",
            "let mut o: OuterP = OuterP { inner: Plain { value: 200 } }; o.inner.value = 5; \
             return need_big(o.inner.value);",
        ),
        (
            "array element place",
            "",
            "let mut a: [Index; 2] = [Index { value: 200 }, Index { value: 300 }]; a[0].value = \
             5; return need_big(a[0].value);",
            "",
            "let mut a: [Plain; 2] = [Plain { value: 200 }, Plain { value: 300 }]; a[0].value = \
             5; return need_big(a[0].value);",
        ),
        (
            "place reached through a &mut borrow",
            "",
            "let mut i: Index = Index { value: 200 }; let r: &mut Index = &mut i; r.value = 5; \
             return need_big(i.value);",
            "",
            "let mut p: Plain = Plain { value: 200 }; let r: &mut Plain = &mut p; r.value = 5; \
             return need_big(p.value);",
        ),
        (
            "store through an @Mut parameter",
            CLOBBER,
            "let mut i: Index = Index { value: 200 }; return clobber(i);",
            CLOBBER_PLAIN,
            "let mut p: Plain = Plain { value: 200 }; return clobber_plain(p);",
        ),
    ] {
        assert_store_decided_by_the_solver(
            form,
            &tool(&format!("{STORE_DECLS}{stale_decls}"), stale),
            &tool(&format!("{STORE_DECLS}{twin_decls}"), twin),
            "T210",
        );
    }
}

/// An actor state field of a refined record type is the same sink: a store into its field in a
/// handler (a `mut` field) or in `init` (any field) carries the obligation, keyed on the field's
/// record type, as a local's does. The twin's field is the clause-free `Plain`.
#[test]
fn a_store_into_a_state_fields_record_is_a_refinement_sink() {
    let head = "module sigil;\ncap type Fuel {}\nrecord Index { value: i64 } where value > 100\n\
                record Plain { value: i64 }\nfn need_big(x: i64) where x > 100 -> i64 {\n    \
                return x;\n}\nentry actor Main { state { fuel: Fuel } on Start() -> i64 { let w \
                = spawn::<Acc>(fuel); return 0; } }\n";
    let actor = |state: &str, init: &str, handler: &str| {
        format!(
            "{head}actor Acc {{\n  state {{ {state} }}\n  init(f: Fuel) {{ {init} }}\n  {handler}\n}}\n"
        )
    };
    let want_twin = BTreeSet::from(["T211".to_string()]);
    for (form, state, init, handler) in [
        (
            "mut field's record stored into in a handler",
            "mut idx: REC",
            "idx = REC { value: 200 };",
            "on Tick() -> i64 { idx.value = 5; return need_big(idx.value); }",
        ),
        (
            "field's record stored into in init",
            "idx: REC",
            "idx = REC { value: 200 }; idx.value = 5; let n: i64 = need_big(idx.value);",
            "on Tick() -> i64 { return 1; }",
        ),
    ] {
        let twin = actor(
            &state.replace("REC", "Plain"),
            &init.replace("REC", "Plain"),
            handler,
        );
        assert_eq!(
            module_codes(&twin),
            want_twin,
            "{form}: the twin without a clause must be refused with T211, or the other form \
             proves nothing"
        );
        let stale = actor(
            &state.replace("REC", "Index"),
            &init.replace("REC", "Index"),
            handler,
        );
        if cfg!(feature = "solver") {
            assert_eq!(
                module_codes(&stale),
                BTreeSet::from(["T210".to_string()]),
                "{form}: a store that breaks the record's invariant was not refused at the \
                 store (DBC-0b regressed)"
            );
        } else {
            assert!(
                sigil_compiler::compile_module(&stale).is_ok(),
                "{form}: refused with {:?} in a build that cannot decide the obligation (the \
                 form is refused statically now, or SR-038 moved)",
                module_codes(&stale)
            );
        }
    }
}

/// A store the collector refuses on its own, in both builds, beside the store of the same shape
/// that keeps the invariant: a value with no fact (T211, as a construction supplying it is
/// refused), a value computed from the field (T211), a compound store, which stores the computed
/// value (T211), and a narrowed value whose bound is weaker than the clause (T215: Z3 refutes
/// the subsumption, and the build without the solver refuses every construction-site
/// subsumption). The kept stores: a literal the clause admits, a value whose fact is the clause
/// (a refined return), and a narrowing with the clause's own bound.
#[test]
fn a_field_store_without_a_fact_for_the_clause_is_refused() {
    let idx = "let mut i: Index = Index { value: 200 };";
    for (form, stale, kept, code) in [
        (
            "a value with no fact",
            "i.value = input; return need_big(i.value);",
            "i.value = 500; return need_big(i.value);",
            "T211",
        ),
        (
            "a value computed from the field",
            "i.value = i.value - 300; return need_big(i.value);",
            "i.value = big(); return need_big(i.value);",
            "T211",
        ),
        (
            "a compound store",
            "i.value -= 300; return need_big(i.value);",
            "if input > 100 { i.value = input; return need_big(i.value); } return 1;",
            "T211",
        ),
        (
            "a narrowed value with a weaker bound",
            "if input > 50 { i.value = input; return need_big(i.value); } return 1;",
            "if input > 100 { i.value = input; return need_big(i.value); } return 1;",
            "T215",
        ),
    ] {
        assert_store_refused_in_both_builds(
            form,
            &tool(STORE_DECLS, &format!("{idx} {stale}")),
            &tool(STORE_DECLS, &format!("{idx} {kept}")),
            code,
        );
    }
}

/// A store into the bound side of a `length()` clause (`len == items.length()`) is refused the
/// same way, T216, while a store into the array side is not joined: the array's length is its
/// type's. Pinned in the build without the solver only: with the solver, constructing any record
/// that declares a `length()` clause reaches Z3's single-value query with the clause unresolved
/// and panics there (`z3_capability::check_refinement`, "LengthOf clauses require their dedicated
/// routes"), before the store is discharged, so the program cannot be compiled in that build at
/// all until the construction emitter resolves the clause; the collector's refusal of the store
/// is what this test pins, and it runs the same in both builds.
#[cfg(not(feature = "solver"))]
#[test]
fn a_store_into_a_length_clauses_bound_field_is_refused() {
    let buf = "record Buf { len: i64, items: [i64; 4] } where len == items.length()\n";
    assert_store_refused_in_both_builds(
        "the clause's bound side",
        &tool(
            buf,
            "let mut b: Buf = Buf { len: 4, items: [1, 2, 3, 4] }; b.len = 3; return 1;",
        ),
        &tool(
            buf,
            "let mut b: Buf = Buf { len: 4, items: [1, 2, 3, 4] }; b.items = [5, 6, 7, 8]; \
             return 1;",
        ),
        "T216",
    );
}

/// A store into a field that a cross-field clause joins to a sibling (`lo <= hi`, either side)
/// is refused outright with T216 in both builds (the spec's Q3: the cross-field code): the other
/// field's current value is not tracked, so the store cannot be checked, and the user
/// reconstructs the record, where both fields are supplied and checked. The kept form is the
/// same store on the clause-free `Span`.
#[test]
fn a_store_into_a_cross_field_clauses_field_is_refused() {
    for (form, field, value) in [
        ("the clause's left side", "lo", "9"),
        ("its right side", "hi", "0"),
    ] {
        assert_store_refused_in_both_builds(
            form,
            &tool(
                STORE_DECLS,
                &format!(
                    "let mut r: Range = Range {{ lo: 1, hi: 5 }}; r.{field} = {value}; return 1;"
                ),
            ),
            &tool(
                STORE_DECLS,
                &format!(
                    "let mut s: Span = Span {{ lo: 1, hi: 5 }}; s.{field} = {value}; return 1;"
                ),
            ),
            "T216",
        );
    }
}

/// A `let` that shadows a refined PARAMETER starts with no fact (DBC0-1): inside
/// `relay(x) where x > 0`, `let x = 0` leaves `need_positive(x)` undischarged, exactly as a
/// binding under a new name does.
#[test]
fn refined_parameter_fact_stops_at_a_binding_that_shadows_it() {
    let relay = |binding: &str| {
        format!(
            "fn relay(x: i64) where x > 0 -> i64 {{\n    let {binding}: i64 = 0;\n    \
             return need_positive({binding});\n}}\n"
        )
    };
    assert_refused_alike(
        "shadowed refined parameter",
        &tool(&relay("x"), "return relay(5);"),
        &tool(&relay("z"), "return relay(5);"),
    );
}

/// A `let` that shadows a NARROWED name starts with no fact (DBC0-1, probe P12): under
/// `if input > 0`, `let input = 0 - 7` leaves `need_positive(input)` undischarged, exactly as a
/// binding under a new name does. A tuple `let` is the same binding site through its desugar,
/// whose entries the second DBC-0a review found written into a frame that was already popped.
#[test]
fn narrowing_fact_stops_at_a_binding_that_shadows_its_name() {
    for (form, stale, twin) in [
        (
            "shadowed narrowed name",
            "if input > 0 { let input: i64 = 0 - 7; return need_positive(input); } return 1;",
            "if input > 0 { let other: i64 = 0 - 7; return need_positive(other); } return 1;",
        ),
        (
            "narrowed name shadowed by a tuple binding",
            "if input > 0 { let (input, z) = (0 - 7, input); return need_positive(input); } \
             return 1;",
            "if input > 0 { let (other, z) = (0 - 7, input); return need_positive(other); } \
             return 1;",
        ),
    ] {
        assert_refused_alike(form, &tool("", stale), &tool("", twin));
    }
}
