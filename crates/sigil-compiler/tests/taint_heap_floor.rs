//! BUG-2 — the HEAP FLOOR on raw memory loads and typed reads (`taint_check.rs`).
//!
//! Taint labels ride on values and on a pointer local's alloc-site region;
//! heap CONTENTS are never labeled, so a `load8` through an address the
//! checker cannot tie to a labeled region reads at the pointer's label. Two
//! verified launders: host-written FFI bytes read through a PREDICTED address
//! (`alloc(1)` then `load8(p + 1)` after `crypto_sha256`), and a stored
//! @Secret read back through a FRESH region's pointer (`load8(b - 1)`). The
//! floor joins every raw load with a monotone per-function floor raised by
//! FFI (S1) and by non-@Public memory writes (S2, keyed on the value's static
//! TYPE at one choke point); the dual channel — a raw store landing inside a
//! live typed aggregate, read back through `a[i]` — is closed by a second
//! floor on typed reads raised only by raw stores (S4).
//!
//! Round 2 closed two more channels found by adversarial review, both
//! reproduced end-to-end: the ADDRESS channel (S6 — a @Public value stored at
//! a @Secret-derived address, raw or through `a[i] = v`, leaves the secret in
//! WHICH cell changed) and the interprocedural STORE direction (S5 — a callee
//! that writes through a pointer its caller handed it). S3, the interprocedural
//! LOAD direction, is still off; its boundary is pinned as an ACCEPT below.
//!
//! Round 3 closed the channel the round-2 review found open on main AND on the
//! branch: a callee's TYPED write through a caller-passed `@Mut` aggregate
//! (`a[0] = s`, `a[s & 1] = 1`, `b.n = s`) now raises the caller's typed-read
//! floor (S5 no longer requires a RAW store for that), joined with the call
//! site's pc. Probing that fix found its intraprocedural twin open too — an
//! ALIAS taken before a projected write (`let b = a; a[0] = s; b[0]`) — closed
//! by S7. Both rules are alias-blind and syntactic; their false positives are
//! pinned as counted costs, not hidden.
//!
//! Round 4 answered the round-3 review's two blockers and what probing them
//! found. `str_from_raw` was a raw read the floor never joined (a forged view
//! is a DEFERRED raw load), so the memory class of EVERY intrinsic is now one
//! total classification (`intrinsic_memory`, pinned name-by-name by the
//! census at the end of this file); the stdlib route (`str_from_bytes` over
//! bytes a secret materialization left behind) needed the interprocedural
//! LOAD direction's result side — S8: a callee that raw-reads returns the
//! CALLER's floor, which also closed the round-3 open pins for a helper or a
//! closure that RETURNS what it read (only the sink-INSIDE-callee form
//! remains, re-pinned below). A callee that only MATERIALIZES a secret
//! aggregate was a fifth channel (round 4, end-to-end on main and round 3);
//! S9 flows a closure body's floors back to its construct site (the `grant`
//! shape); S10 seeds every actor `init`/handler at the fixpoint of what all of
//! them leave in the state heap, and treats every state-field read as a
//! typed memory read (a scalar state cell is memory too).
//!
//! Round 5 answered the round-4 review's blocker: string literal bytes are
//! SHARED STATIC DATA (one copy per distinct literal from offset 1024, each
//! use allocating only a header), so S8's premise that a named callee's typed
//! reads reach only its own fresh cells was false — `fn peek() { "AAAAAAAA"
//! .byte_at(3) }` returned the caller's raw-stored secret end-to-end (2a / 07)
//! on main and round 4, and so did two literals compared in ONE function and
//! an f-string in a callee. S11 makes a `str` literal / f-string a typed read
//! and drops the premise: a named callee with ANY typed read is `reads_typed`.
//! The S9 switch is no longer pinned by a const assertion — the one test that
//! depends on it branches at runtime, so S9 is measurable off like S3.
//!
//! Round 6 answered the landing review's seventh channel — and the sink it
//! named. The floors label what a READ returns; a pointer reaches a sink
//! UNREAD when `tool_main` returns `out << 32 | n` and the HOST reads the
//! buffer. That sink's rule is the M6 REGION taint, written until then by one
//! arm (an expression-statement `store8`, value operand only), so a callee
//! minting a @Secret and storing it through the caller's pointer, the address
//! channel `store8(out + (s & 1), 9)`, `vec_store`, a two-deep alias chain and
//! a closure storing behind a captured pointer were each accepted and each
//! printed the bit on main. The rule is now total on three sides — inline
//! (every raw write, every operand, joined with the pc), at a call site (the
//! summary names the parameter SLOTS a write can go through, transitive over
//! the call graph) and at a closure's construct site.
//!
//! Round 7 answered the round-6 review's two findings on that sink. The OPEN
//! surface is wider than "a pointer smuggled through memory": the M6 model
//! regions only locals derived from `alloc` by `+`/`-`, so a raw write through
//! ANY other pointer expression — `tool_main`'s own `input_ptr` (the host's
//! buffer, the most natural tool shape), a callee's result, other arithmetic,
//! a pointer reloaded from memory or read out of an aggregate or a state
//! field — is attributed to no region; the parameter and record-field shapes
//! are pinned as exact ACCEPTS beside the array-element one. And the region
//! facts were joined at NO control-flow merge (the loop fixpoint dropped them,
//! `if`/`match` arms shared one map, a shadow left its region behind): a
//! REGIONED local in the WRONG region at the store, a class of its own,
//! closed — the region map is a per-path fact joined by union and loop-carried.
//!
//! Round 8 answered the round-7 review's one blocker: the criterion sentence
//! over-claimed. Only a value that WAS the `alloc` call minted a region at a
//! `let`/rebind, and `region_of_expr` gave a bare `alloc(..)` operand none, so
//! `let q: i64 = alloc(8) + 0; store8(q, s & 1); return q << 32 | 1` was
//! accepted on main and on round 7 (`forge` printed the bit) although every
//! disclosure called such a `q` "derived from `alloc` by `+`/`-`". The binding
//! is now total over the chain (`regions_of_bound_value`: every `alloc` leaf
//! mints, every local leaf contributes, a mixed chain is attributed to both),
//! so the model regions exactly the locals bound to `alloc`, or to `+`/`-`
//! arithmetic over `alloc` calls and regioned locals — and the sentence at
//! every disclosure site says that.
//!
//! Every test asserts the EXACT diagnostic code set. The clean twins are the
//! over-taint fences, the anti-stubs prove S5 keys on the WRITE and not on a
//! secret anywhere in the call graph and that the census sees a planted
//! variant, the counted-false-positive pins record what the coarse rules
//! cost, and the accepting tests pin the channels that remain open (the S3
//! boundary flips with `HEAP_FLOOR_PROGRAM_ENTRY`).

use std::collections::{BTreeMap, BTreeSet};

use sigil_compiler::taint_check::{
    HEAP_FLOOR_ACTOR_DISPATCH, HEAP_FLOOR_AFTER_FFI, HEAP_FLOOR_AFTER_STORE,
    HEAP_FLOOR_CALLEE_READS, HEAP_FLOOR_CALLEE_WRITES, HEAP_FLOOR_CLOSURE_FLOWS_BACK,
    HEAP_FLOOR_PROGRAM_ENTRY, HEAP_FLOOR_RAW_STORE_TYPED_READS, HEAP_FLOOR_STATIC_READS,
    HEAP_FLOOR_TYPED_WRITE_TYPED_READS,
};
use sigil_test_utils::pipeline::{compile_module_codes, compile_tool_codes};

/// Trusted outer-ring tool header with the grant-free digest extern (the
/// host writes the 32-byte digest at the guest's own bump pointer).
const TOOL_HDR: &str = "#[ring(outer)] #[trusted] module tool;\n\
     extern \"C\" fn crypto_sha256(input: i32, input_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn pub_sink(x: i64 @Public) -> i64 @Public {\n    return x;\n}\n";

const TOOL_MAIN: &str = "pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {\n\
     \x20   return probe(input_ptr, input_len);\n}\n";

const MOD_HDR: &str = "#[ring(outer)] module ext;\n\
     fn pub_sink(x: i64 @Public) -> i64 @Public {\n    return x;\n}\n";

fn tool_code_set(probe: &str) -> BTreeSet<String> {
    compile_tool_codes(&format!("{TOOL_HDR}{probe}{TOOL_MAIN}"))
        .into_iter()
        .collect()
}

fn module_code_set(body: &str) -> BTreeSet<String> {
    compile_module_codes(&format!("{MOD_HDR}{body}"))
        .into_iter()
        .collect()
}

/// The same trusted tool shape as `TOOL_HDR`, but named `string`: the one
/// module the `str_from_raw` gate admits, so a probe can forge a `str` view
/// over raw memory the way the stdlib builders do.
const STRING_HDR: &str = "#[ring(outer)] #[trusted] module string;\n\
     extern \"C\" fn crypto_sha256(input: i32, input_len: i32) -> i64 ! { FFI, Unsafe };\n\
     fn pub_sink(x: i64 @Public) -> i64 @Public {\n    return x;\n}\n";

fn string_code_set(probe: &str) -> BTreeSet<String> {
    compile_tool_codes(&format!("{STRING_HDR}{probe}{TOOL_MAIN}"))
        .into_iter()
        .collect()
}

/// A plain (inner-ring) tool module — the header an actor with `grant` or a
/// `use sigil::string;` program carries in the corpus.
const PLAIN_HDR: &str =
    "module tool;\nfn pub_sink(x: i64 @Public) -> i64 @Public {\n    return x;\n}\n";

fn plain_code_set(body: &str) -> BTreeSet<String> {
    compile_module_codes(&format!("{PLAIN_HDR}{body}"))
        .into_iter()
        .collect()
}

/// A stand-in for the stdlib `string` module's `str_from_bytes`, in the SAME
/// shape (forge a view over the caller's bytes, copy them into a fresh
/// buffer through `byte_at`, forge the result): the callee raw-reads through
/// `str_from_raw` and stores only what it read, and its own floors start
/// clean. Composed in front of a plain `module tool; use sigil::string;`
/// program exactly as the bench harness composes the real stdlib.
const STRING_STDLIB: &str = "module string;\n\
     pub fn str_from_bytes(ptr: i64, len: i64) -> Option<str> ! { Alloc } {\n\
     \x20   let view: str = str_from_raw(ptr, len);\n\
     \x20   let buf: i64 = alloc(len);\n\
     \x20   let mut i: i64 = 0;\n\
     \x20   while i < len {\n\
     \x20       store8(buf + i, view.byte_at(i));\n\
     \x20       i = i + 1;\n\
     \x20   }\n\
     \x20   return Some(str_from_raw(buf, len));\n}\n";

fn composed_code_set(body: &str) -> BTreeSet<String> {
    compile_module_codes(&format!(
        "{STRING_STDLIB}module tool;\nuse sigil::string;\n\
         fn pub_sink(x: i64 @Public) -> i64 @Public {{\n    return x;\n}}\n{body}"
    ))
    .into_iter()
    .collect()
}

fn set(codes: &[&str]) -> BTreeSet<String> {
    codes.iter().map(|c| (*c).to_owned()).collect()
}

/// An S11 pin: exactly `T001` with the switch on; with it OFF, the round-4
/// behavior — the program is ACCEPTED (every one of these shapes was
/// `check` clean and leaked end-to-end on the round-4 binary). Branching at
/// runtime instead of pinning the switch at compile time is what makes S11
/// measurable off (the round-4 review's S9 complaint, applied to the new rule).
fn assert_t001_when_s11_on(codes: &BTreeSet<String>, on_msg: &str) {
    if HEAP_FLOOR_STATIC_READS {
        assert_eq!(*codes, set(&["T001"]), "{on_msg}");
    } else {
        assert!(
            codes.is_empty(),
            "S11 OFF is the round-4 hole: literals are not reads and named callees never \
             `reads_typed`, so the program is accepted — measured, not wanted; got {codes:?}"
        );
    }
}

/// The file's assumptions about the switch configuration are pinned, so a
/// flipped switch fails HERE with a name rather than in a downstream twin.
/// The switches are `const`, so the pin is a const block (evaluated at
/// compile time; `clippy::assertions_on_constants` rejects a runtime
/// `assert!` on a constant) — flipping one is a compile error of this file.
#[test]
fn heap_floor_switch_configuration_is_pinned() {
    const {
        assert!(
            HEAP_FLOOR_AFTER_FFI,
            "S1 must be on for the FFI tests below"
        );
        assert!(
            HEAP_FLOOR_AFTER_STORE,
            "S2 must be on for the store tests below"
        );
        assert!(
            HEAP_FLOOR_RAW_STORE_TYPED_READS,
            "S4 must be on for the typed-read tests below"
        );
        assert!(
            HEAP_FLOOR_CALLEE_WRITES,
            "S5 must be on for the interprocedural-store tests below"
        );
        assert!(
            HEAP_FLOOR_TYPED_WRITE_TYPED_READS,
            "S7 must be on for the alias tests below"
        );
        assert!(
            !HEAP_FLOOR_PROGRAM_ENTRY,
            "S3 must be OFF for the open-channel pins at the end of this file: \
             whoever measures S3 on must re-derive those pins, not skip them"
        );
        assert!(
            HEAP_FLOOR_CALLEE_READS,
            "S8 must be on for the callee-read tests below"
        );
        // S9 (`HEAP_FLOOR_CLOSURE_FLOWS_BACK`) and S11 (`HEAP_FLOOR_STATIC_READS`)
        // are deliberately NOT pinned here: the tests that depend on them
        // branch on the switch at runtime, the way the S3 pins do, so each can
        // be measured OFF without this binary failing to compile (round-5
        // review). S9 off was measured at exactly one red pin (round 4's 104
        // tests: 103 / 1); S11 off is the round-4 behavior every S11 pin's
        // `else` branch records.
        assert!(
            HEAP_FLOOR_ACTOR_DISPATCH,
            "S10 must be on for the actor dispatch tests below"
        );
    }
}

/// BUG-2 repro: the digest byte at `p + 1` (host-written) reaches a @Public
/// sink through `p`'s @Public label. The floor raised by the extern call
/// makes the load @Internal.
#[test]
fn ffi_digest_read_through_predicted_address_is_t001() {
    let codes = tool_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return pub_sink(load8(p + 1));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "predicted-address FFI read must be T001"
    );
}

/// BUG-2 full-buffer variant: all 32 digest bytes hex-encoded in a loop.
#[test]
fn ffi_digest_loop_read_through_predicted_addresses_is_t001() {
    let codes = tool_code_set(
        "fn hex_char(v: i64 @Public) -> i64 @Public {\n\
         \x20   if v < 10 {\n        return 48 + v;\n    } else {\n        return 87 + v;\n    }\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 32 {\n\
         \x20       let b: i64 = pub_sink(load8(p + 1 + i));\n\
         \x20       store8(out + i * 2, hex_char(b >> 4));\n\
         \x20       store8(out + i * 2 + 1, hex_char(b & 15));\n\
         \x20       i += 1;\n\
         \x20   }\n\
         \x20   return out << 32 | 64;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "looped predicted-address FFI reads must be T001"
    );
}

/// CONTROL: the same byte read through the RETURNED pointer was already
/// rejected (the packed result is @Internal) and must stay rejected.
#[test]
fn ffi_digest_read_through_returned_pointer_is_still_t001() {
    let codes = tool_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let packed: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   let digest_ptr: i64 @Internal = packed / 4294967296;\n\
         \x20   return pub_sink(load8(digest_ptr));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "returned-pointer read must remain T001"
    );
}

/// CLEAN TWIN: no FFI and no store — nothing raised the floor, so the
/// identical predicted-address read is still @Public (the byte is the
/// zero-filled page). Fences the floor against firing with no cause.
#[test]
fn predicted_address_read_with_no_ffi_and_no_store_is_clean() {
    let codes = compile_tool_codes(
        "#[ring(outer)] #[trusted] module tool;\n\
         fn pub_sink(x: i64 @Public) -> i64 @Public {\n    return x;\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(p + 1));\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   return probe(input_ptr, input_len);\n}\n",
    );
    assert!(codes.is_empty(), "no cause, no floor; got {codes:?}");
}

/// CLEAN TWIN: a load BEFORE the extern call reads bytes the host has not
/// written yet, so it stays @Public — the floor is flow-sensitive, not a
/// function-wide blanket. (S3 makes it a blanket by design; pinned below.)
#[test]
fn load_before_the_ffi_call_stays_public() {
    let codes = tool_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let b: i64 = load8(p);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return pub_sink(b);\n}\n",
    );
    if HEAP_FLOOR_PROGRAM_ENTRY {
        assert_eq!(
            codes,
            set(&["T001"]),
            "S3 floors every load in an FFI program"
        );
    } else {
        assert!(
            codes.is_empty(),
            "a load before FFI must stay clean; got {codes:?}"
        );
    }
}

/// Loop-carried FFI: the load precedes the extern call LEXICALLY but follows
/// it in iteration two. The floor is part of the loop fixpoint state.
#[test]
fn ffi_late_in_loop_floors_the_load_before_it_is_t001() {
    let codes = tool_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let mut acc: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       acc = acc + pub_sink(load8(p + 1));\n\
         \x20       let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20       i += 1;\n\
         \x20   }\n\
         \x20   return acc;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "loop-carried FFI must floor the earlier load"
    );
}

/// The host boundary reached through a CALLEE whose effect row carries `FFI`
/// raises the caller's floor just like a direct extern call.
#[test]
fn ffi_through_callee_with_ffi_row_floors_the_caller_is_t001() {
    let codes = tool_code_set(
        "fn hash(input_ptr: i32, input_len: i32) -> i64 @Internal ! { FFI, Unsafe } {\n\
         \x20   return crypto_sha256(input_ptr, input_len);\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let unused: i64 @Internal = hash(input_ptr, input_len);\n\
         \x20   return pub_sink(load8(p + 1));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an FFI-row callee must raise the floor"
    );
}

/// The interprocedural LOAD direction, RESULT side (S8, round 4 — was the
/// pinned open boundary through round 3): a helper that loads through its
/// pointer parameter is checked with its own (clean) floor, but its RESULT
/// comes back to a caller whose floor is @Internal after the FFI, and a
/// callee that raw-reads returns the caller's floor. The round-3 build
/// accepted this and `sigil forge` emitted the digest byte (227 for input
/// "", 62 for "b").
#[test]
fn helper_returning_a_raw_read_after_callers_ffi_is_t001() {
    let codes = tool_code_set(
        "fn peek(p: i64) -> i64 @Public {\n\
         \x20   return load8(p + 1);\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return pub_sink(peek(p));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a raw-reading helper's result must carry the caller's post-FFI floor"
    );
}

/// Clean twin of S8: the same helper called BEFORE the FFI reads a clean
/// floor, and a helper that reads nothing raw returns nothing floored.
#[test]
fn helper_returning_a_raw_read_before_callers_ffi_is_clean() {
    let codes = tool_code_set(
        "fn peek(p: i64) -> i64 @Public {\n\
         \x20   return load8(p + 1);\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let early: i64 = pub_sink(peek(p));\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return early;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a raw read before the FFI must stay clean through a helper too; got {codes:?}"
    );
}

/// THE INTERPROCEDURAL BOUNDARY that REMAINS after S8, pinned: the helper
/// SINKS the raw read inside itself, where its own (clean) floor is all it
/// sees, and the caller DISCARDS the result into a @Secret binding. S8
/// floors what comes OUT of a callee — the result of a raw-reading callee
/// carries the caller's floor whether or not the callee returned the read,
/// so `return peek(p)` and a plain `let ignored: i64 = peek(p)` from this
/// probe are both rejected — not what happens INSIDE it. Only S3 (every
/// function starts at the program-wide floor) rejects this form. Whoever
/// flips S3 must flip this expectation with it.
#[test]
fn helper_sinking_a_raw_read_inside_itself_after_callers_ffi_is_the_interprocedural_boundary() {
    let codes = tool_code_set(
        "fn peek(p: i64) -> i64 @Public {\n\
         \x20   let leaked: i64 = pub_sink(load8(p + 1));\n\
         \x20   return 0;\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   let ignored: i64 @Secret = peek(p);\n\
         \x20   return 0;\n}\n",
    );
    if HEAP_FLOOR_PROGRAM_ENTRY {
        assert_eq!(
            codes,
            set(&["T001"]),
            "S3 closes the interprocedural boundary"
        );
    } else {
        assert!(
            codes.is_empty(),
            "S8 floors a callee's RESULT, not a sink inside it: this launder is the \
             documented boundary; got {codes:?}"
        );
    }
}

/// No-FFI launder: a @Secret stored through `a` is read back through `b - 1`
/// (a fresh region; `alloc` is an unaligned bump, so `b - 1 == a`). The
/// region model taints region `a` only; the store floor catches the read.
#[test]
fn secret_store_read_back_through_fresh_region_is_t001() {
    let codes = module_code_set(
        "fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   store8(a, s);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 1));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "cross-region secret read-back must be T001"
    );
}

/// CONTROL: the same store read back through the OWNING pointer was already
/// rejected by the region model and stays rejected.
#[test]
fn secret_store_read_back_through_owning_region_is_still_t001() {
    let codes = module_code_set(
        "fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   store8(a, s);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(a));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "same-region read-back must remain T001"
    );
}

/// Loop-carried secret store: the load precedes the store lexically but
/// follows it in iteration two. The region model misses this (the fixpoint
/// passes carry no regions, and the real pass reads before it stores); the
/// loop-carried floor catches it. Accepted on main before the floors.
#[test]
fn secret_store_late_in_loop_floors_the_load_before_it_is_t001() {
    let codes = module_code_set(
        "fn f(s: i64 @Secret) -> i64 ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   let mut acc: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       acc = acc + load8(p);\n\
         \x20       store8(p, s);\n\
         \x20       i += 1;\n\
         \x20   }\n\
         \x20   return acc;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "loop-carried secret store must floor the earlier load"
    );
}

/// A materialized aggregate with a @Secret field is a memory write: a raw
/// load anywhere after it is floored at @Secret.
#[test]
fn secret_record_construct_floors_a_later_raw_load_is_t001() {
    let codes = module_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let pt: Point @Secret = Point { x: s, y: 0 };\n\
         \x20   return pub_sink(load8(p));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a secret aggregate in memory must floor later raw loads"
    );
}

/// S2 by TYPE, not by constructor arm: `Ok(s)` lowers to a heap record
/// holding the secret (`air.rs` `lower_result_ctor`), and a per-arm list
/// missed it (round 1 accepted this). Fenced at the choke point.
#[test]
fn secret_result_ctor_floors_a_later_raw_load_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let r: Result<i64, u32> @Secret = Ok(s);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 8));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a secret Result in memory must floor"
    );
}

/// Same class: `u256_from_i64(s)` bump-allocates a fresh 32-byte cell holding
/// the secret limb; the intrinsic arm returned `args_taint` without noting the
/// write. Keyed on `Type::U256` now.
#[test]
fn secret_u256_cell_floors_a_later_raw_load_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let u: u256 @Secret = u256_from_i64(s);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 32));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a secret u256 cell in memory must floor"
    );
}

/// Same class through a CALL: the aggregate is materialized in the callee and
/// only its pointer comes back, so no constructor arm runs in this function at
/// all. The call expression's heap-resident type is what notes the write.
#[test]
fn secret_record_returned_from_callee_floors_a_later_raw_load_is_t001() {
    let codes = module_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn mk(s: i64 @Secret) -> Point @Secret ! { Alloc } {\n\
         \x20   return Point { x: s, y: 0 };\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let pt: Point @Secret = mk(s);\n\
         \x20   return pub_sink(load8(p));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee-built secret aggregate is in memory too"
    );
}

/// A heap-typed @Secret PARAMETER's bytes are already in memory at entry (the
/// caller wrote them), so the floor starts raised without any write in the body.
#[test]
fn secret_record_parameter_floors_a_raw_load_at_entry_is_t001() {
    let codes = module_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn probe(pt: Point @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(p));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a secret aggregate parameter must floor"
    );
}

/// A SCALAR @Secret parameter lives in a wasm local, not in memory: no floor.
/// Fences the parameter rule against firing on every secret scalar.
#[test]
fn secret_scalar_parameter_does_not_raise_the_floor() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(p));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a scalar param is not in memory; got {codes:?}"
    );
}

/// S4 — THE DUAL CHANNEL (verified end-to-end on main: forge returns 42): a
/// @Secret raw-stored at a predicted bump address lands inside the array
/// literal allocated after `b`, and the TYPED read `a[0]` returns it as
/// @Public. The raw store raises the typed-read floor, so `a[0]` is @Secret.
#[test]
fn secret_raw_store_into_typed_array_read_back_via_index_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let a: [i64; 2] = [0, 0];\n\
         \x20   let mut i: i64 = 1;\n\
         \x20   while i < 65 {\n\
         \x20       store8(b + i, s);\n\
         \x20       i += 1;\n\
         \x20   }\n\
         \x20   return pub_sink(a[0] & 255);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a raw secret store must floor typed reads"
    );
}

/// S4 through a record field read, with the store OUTSIDE any loop.
#[test]
fn secret_raw_store_then_record_field_read_is_t001() {
    let codes = module_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let pt: Point = Point { x: 0, y: 0 };\n\
         \x20   store8(b + 1, s);\n\
         \x20   return pub_sink(pt.x);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a raw secret store must floor field reads"
    );
}

/// S4 CLEAN TWIN: an FFI call writes only FRESH host cells, which no live typed
/// value overlaps, so it must NOT floor typed reads — a tool that parses its own
/// record after an extern call keeps @Public fields.
#[test]
fn ffi_does_not_floor_typed_reads() {
    let codes = tool_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let pt: Point = Point { x: 1, y: 2 };\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return pub_sink(pt.x);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "FFI initializes fresh cells only; got {codes:?}"
    );
}

/// S4 CLEAN TWIN: materializing a secret aggregate initializes a FRESH cell
/// and touches no live typed value, so a public record's field stays @Public
/// (only the RAW-load floor rises, and no raw load happens here).
#[test]
fn secret_materialization_does_not_floor_typed_reads() {
    let codes = module_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let pt: Point = Point { x: 1, y: 2 };\n\
         \x20   let sp: Point @Secret = Point { x: s, y: 0 };\n\
         \x20   return pub_sink(pt.x);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a materialization is not a raw store; got {codes:?}"
    );
}

/// CLEAN TWIN for the store floor: a @Public store does not raise the floor,
/// so a later cross-region read is still @Public.
#[test]
fn public_store_does_not_raise_the_floor() {
    let codes = module_code_set(
        "fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   store8(a, 7);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 1));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store must not raise the floor; got {codes:?}"
    );
}

/// A store under a @Secret branch leaks the branch through memory even when
/// the stored VALUE is public: the floor joins the effective pc.
#[test]
fn public_store_under_secret_branch_floors_a_later_load_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   if s > 0 {\n        store8(a, 1);\n    }\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 1));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a secret-guarded store must floor later loads"
    );
}

// ---------------------------------------------------------------------------
// S6 — THE ADDRESS CHANNEL. What a store WRITES is not the only thing it
// leaves behind: WHICH cell it touched is an observation too. Every probe
// below stores a @Public value and was ACCEPTED by round 1
// (found by adversarial review). Two are demonstrated END-TO-END with
// `sigil forge`: the one-bit raw-store probe (secret 40 -> 0 bytes of output,
// 41 -> 9 bytes) and the typed `a[s & 1] = 1` probe (40 -> 1 byte, 41 -> 0).
// The loop and the twin fences are static.
// ---------------------------------------------------------------------------

/// The raw-store address channel: the stored value is the @Public constant 9,
/// and the secret is the bit that selects the cell. Read back through a fresh
/// region's pointer.
#[test]
fn public_value_stored_at_a_secret_address_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(2);\n\
         \x20   store8(a + (s & 1), 9);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 1));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a @Public value at a @Secret address is a @Secret write"
    );
}

/// COUNTED COST of "every intrinsic result is a typed read": after a
/// non-@Public raw store, `let b: i64 = alloc(1)` in the same function is
/// rejected — `alloc` returns a fresh pointer and reads no memory, but
/// `reads_typed_memory` treats every intrinsic as a read of floored memory and
/// the unannotated binding is a @Public sink. main at ae026aec accepts this
/// program (`check` clean, both binaries measured at landing). Found by the
/// precision-corpus fixtures, which count T001 per sink where this file's
/// code SETS could not: a narrower rule would classify intrinsics by
/// `intrinsic_memory` (an allocation is not a read) — an author decision
/// recorded in the landing decision record, not taken here.
#[test]
fn let_binding_of_an_alloc_after_a_secret_raw_store_is_a_counted_false_positive() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   store8(a, s);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return 0;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the coarse intrinsic rule floors an allocation's pointer: a counted cost, not a claim"
    );
}

/// The address channel is not one bit: a loop walks the secret out byte by
/// byte, every stored value the @Public constant 1.
#[test]
fn secret_address_walked_out_in_a_loop_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 6 {\n\
         \x20       store8(a + ((s >> i) & 1), 1);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 7));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a loop-carried secret address must floor the read-back"
    );
}

/// S6 OVER-TAINT FENCE: the same shape with a @Public index must stay clean —
/// the rule keys on the address's LABEL, not on address arithmetic.
#[test]
fn public_store_at_a_public_computed_address_is_clean() {
    let codes = module_code_set(
        "fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(2);\n\
         \x20   store8(a + (k & 1), 9);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 1));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a computed PUBLIC address must not raise the floor; got {codes:?}"
    );
}

/// S6 on the TYPED side: no raw store at all — `a[s & 1] = 1` writes a @Public
/// value into a bounds-checked array slot, and `a[0]` reads the secret's low
/// bit back. Verified end-to-end before the fix (`sigil forge` returns 1 byte
/// for secret 40 and 0 bytes for 41).
#[test]
fn typed_store_at_a_secret_index_read_back_via_index_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   a[s & 1] = 1;\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a typed store at a @Secret index must floor typed reads"
    );
}

/// S6 TYPED OVER-TAINT FENCE: the same program with a @Public index — the
/// ordinary way every loop writes an array — must stay clean.
#[test]
fn typed_store_at_a_public_index_is_clean() {
    let codes = module_code_set(
        "fn probe(i: i64 @Public) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   a[i & 1] = 1;\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public index must not raise the floor; got {codes:?}"
    );
}

// ---------------------------------------------------------------------------
// S5 — THE INTERPROCEDURAL STORE DIRECTION. A callee that writes memory
// through a pointer its caller handed it is invisible to every
// flow-sensitive rule in the caller's own body. Every probe below was ACCEPTED
// by round 1, while the SAME program written in one function
// was already rejected. Exactly one of them is demonstrated END-TO-END: the
// callee-minted secret below is exfiltrated by `sigil forge` (42 bytes of
// output for secret 42, 7 for 7, 0 with the store deleted). The other two are
// static rejections of that same channel, not separate demonstrations.
// ---------------------------------------------------------------------------

/// The secret never crosses the call boundary as an argument: the callee MINTS
/// it and stores it through the caller's pointer. Only the callee's own
/// annotation bound can see it.
#[test]
fn callee_stores_its_own_secret_through_the_callers_pointer_is_t001() {
    let codes = module_code_set(
        "fn stash(p: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   store8(p, s);\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   let ignored: i64 = stash(a);\n\
         \x20   return pub_sink(load8(a));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's store must raise the CALLER's raw-load floor"
    );
}

/// The S4 dual, one call deep: the callee's RAW store can land inside a live
/// typed aggregate of the caller, so the caller's TYPED reads are floored too.
#[test]
fn callee_raw_store_floors_the_callers_typed_read_is_t001() {
    let codes = module_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn stash(p: i64, s: i64 @Secret) -> i64 ! {} {\n\
         \x20   store8(p + 1, s);\n\
         \x20   return 0;\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let pt: Point = Point { x: 0, y: 0 };\n\
         \x20   let unused: i64 @Secret = stash(b, s);\n\
         \x20   return pub_sink(pt.x);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's raw store must raise the CALLER's typed-read floor"
    );
}

/// S5 where the stored label comes from the HOST, not from an annotation: the
/// callee calls `crypto_sha256` and raw-stores a digest byte through the
/// caller's pointer, with no taint annotation anywhere in its body. S1 floors
/// the caller's raw loads for an FFI-row callee but deliberately not its typed
/// reads, so only the @Internal in the callee's summary catches the digest byte
/// landing inside the caller's live record.
#[test]
fn callee_that_stores_an_ffi_result_floors_the_callers_typed_read_is_t001() {
    let codes = tool_code_set(
        "record Point { x: i64, y: i64 }\n\
         fn stash(p: i64, ip: i32, il: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   store8(p + 1, load8(crypto_sha256(ip, il) + 1));\n\
         \x20   return 0;\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let pt: Point = Point { x: 0, y: 0 };\n\
         \x20   let ignored: i64 = stash(b, input_ptr, input_len);\n\
         \x20   return pub_sink(pt.x);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's FFI-derived raw store must floor the caller's typed reads"
    );
}

/// S5 ANTI-STUB: the identical program with the callee's `store8` DELETED —
/// the @Secret annotation still sits in the callee — must stay clean. This is
/// what proves the rejection above comes from the WRITE and not from the mere
/// presence of a secret anywhere in the call graph.
#[test]
fn callee_that_stores_nothing_does_not_raise_the_callers_floor() {
    let codes = module_code_set(
        "fn stash(p: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   let ignored: i64 = stash(a);\n\
         \x20   return pub_sink(load8(a));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a callee that writes nothing must not raise the floor; got {codes:?}"
    );
}

/// S5 OVER-TAINT FENCE: a helper that fills a buffer with @Public bytes — the
/// shape every stdlib writer has — must not raise the caller's floor.
#[test]
fn callee_that_stores_only_public_bytes_does_not_raise_the_callers_floor() {
    let codes = module_code_set(
        "fn fill(p: i64) -> i64 @Public {\n\
         \x20   store8(p, 7);\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let a: i64 = alloc(1);\n\
         \x20   let ignored: i64 = fill(a);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(load8(b - 1));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public-only writer must not raise the floor; got {codes:?}"
    );
}

// ---------------------------------------------------------------------------
// S5, ROUND 3 — TYPED WRITES THROUGH A `@Mut` PARAMETER. Round 2 raised the
// caller's TYPED-read floor only for a callee that could RAW-store, so a callee
// that wrote its own secret into the caller's aggregate with an ordinary typed
// assignment was read back as @Public. Found by the round-2 adversarial review
// and verified END-TO-END with `sigil forge` on BOTH the round-2 branch and main
// at ae026aec (a pre-existing hole, not a regression): the value form returned
// 42 bytes of output for secret 42 and 7 for 7; the index form `a[s & 1] = 1`
// returned 0 bytes for secret 40 and 1 for 41; the record-field form `b.n = s`
// returned 42 / 7. Every probe has a CLEAN TWIN (the same shape moving only
// @Public bytes) that must stay accepted, and the one twin the rule
// necessarily rejects is pinned as a counted false positive.
// ---------------------------------------------------------------------------

/// Value form: the callee MINTS the secret and writes it into the caller's
/// array through `@Mut`. End-to-end repro (42 / 7 bytes before the fix).
#[test]
fn callee_typed_write_of_its_own_secret_through_mut_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's typed write through @Mut must floor the CALLER's typed reads"
    );
}

/// Clean twin of the value form: the identical callee writing an unlabeled
/// value must stay accepted.
#[test]
fn callee_typed_write_of_a_public_value_through_mut_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public typed write through @Mut must not raise the floor; got {codes:?}"
    );
}

/// Index form: a @Public value at a callee-secret INDEX — which cell changed
/// is the secret. End-to-end repro (0 / 1 byte before the fix).
#[test]
fn callee_typed_write_at_its_own_secret_index_through_mut_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 41;\n\
         \x20   a[s & 1] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(a[1]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's write at a secret index must floor the CALLER's typed reads"
    );
}

/// Clean twin of the index form.
#[test]
fn callee_typed_write_at_a_public_index_through_mut_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 41;\n\
         \x20   a[s & 1] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(a[1]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public index through @Mut must not raise the floor; got {codes:?}"
    );
}

/// Record-field form. End-to-end repro (42 / 7 bytes before the fix).
#[test]
fn callee_record_field_write_of_its_own_secret_through_mut_is_t001() {
    let codes = module_code_set(
        "record Bag { n: i64, m: i64 }\n\
         fn poke(b: Bag @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   b.n = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut b: Bag = Bag { n: 0, m: 0 };\n\
         \x20   let ignored: i64 = poke(b);\n\
         \x20   return pub_sink(b.n);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's field write through @Mut must floor the CALLER's typed reads"
    );
}

/// Clean twin of the record-field form.
#[test]
fn callee_record_field_write_of_a_public_value_through_mut_is_clean() {
    let codes = module_code_set(
        "record Bag { n: i64, m: i64 }\n\
         fn poke(b: Bag @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 42;\n\
         \x20   b.n = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut b: Bag = Bag { n: 0, m: 0 };\n\
         \x20   let ignored: i64 = poke(b);\n\
         \x20   return pub_sink(b.n);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public field write through @Mut must not raise the floor; got {codes:?}"
    );
}

/// Nested place: a secret index inside a record's array field.
#[test]
fn callee_nested_write_at_its_own_secret_index_through_mut_is_t001() {
    let codes = module_code_set(
        "record Bag { data: [i64; 2], n: i64 }\n\
         fn poke(b: Bag @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 41;\n\
         \x20   b.data[s & 1] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut b: Bag = Bag { data: [0, 0], n: 0 };\n\
         \x20   let ignored: i64 = poke(b);\n\
         \x20   return pub_sink(b.data[1]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a nested secret-index write through @Mut must floor the caller"
    );
}

/// Clean twin of the nested form.
#[test]
fn callee_nested_write_at_a_public_index_through_mut_is_clean() {
    let codes = module_code_set(
        "record Bag { data: [i64; 2], n: i64 }\n\
         fn poke(b: Bag @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 41;\n\
         \x20   b.data[s & 1] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut b: Bag = Bag { data: [0, 0], n: 0 };\n\
         \x20   let ignored: i64 = poke(b);\n\
         \x20   return pub_sink(b.data[1]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a nested public-index write must not raise the floor; got {codes:?}"
    );
}

/// Two levels: the writer is reached only through a forwarding `@Mut` callee,
/// so the summary must be TRANSITIVE.
#[test]
fn callee_typed_write_two_calls_deep_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn mid(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   return poke(a);\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = mid(a);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a transitive callee's typed write must floor the caller"
    );
}

/// Clean twin of the two-level form.
#[test]
fn callee_public_typed_write_two_calls_deep_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn mid(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   return poke(a);\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = mid(a);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a transitive public writer must not raise the floor; got {codes:?}"
    );
}

/// The secret reaches the callee as a `@Flow` INDEX argument: no annotation
/// in the callee sees it, only the call site's argument join. (With a
/// `@Secret`-declared index parameter the program is rejected regardless of
/// the argument — see the counted false positive below.)
#[test]
fn flow_callee_write_at_a_secret_index_argument_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut, i: i64 @Flow) -> i64 @Flow {\n\
         \x20   a[i & 1] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 @Secret = poke(a, s);\n\
         \x20   return pub_sink(a[1]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a secret index argument must floor the caller through the arg join"
    );
}

/// Clean twin: the same `@Flow` callee called with a @Public index.
#[test]
fn flow_callee_write_at_a_public_index_argument_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut, i: i64 @Flow) -> i64 @Flow {\n\
         \x20   a[i & 1] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a, k);\n\
         \x20   return pub_sink(a[1]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public index argument must not raise the floor; got {codes:?}"
    );
}

/// The pc channel: a `@Flow` callee writes a CONSTANT, but only under the
/// caller's secret branch. Verified end-to-end before the fix (0 bytes for
/// secret 40, 1 for 41); only the call site's pc join catches it.
#[test]
fn flow_callee_write_under_the_callers_secret_branch_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Flow @Mut) -> i64 @Flow {\n\
         \x20   a[0] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   if (s & 1) == 1 {\n\
         \x20       let ignored: i64 @Secret = poke(a);\n\
         \x20   }\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's write under a secret branch must floor the caller"
    );
}

/// Clean twin: the same call under a @Public branch.
#[test]
fn flow_callee_write_under_a_public_branch_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Flow @Mut) -> i64 @Flow {\n\
         \x20   a[0] = 1;\n\
         \x20   return 0;\n}\n\
         fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   if (k & 1) == 1 {\n\
         \x20       let ignored: i64 = poke(a);\n\
         \x20   }\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a write under a public branch must not raise the floor; got {codes:?}"
    );
}

/// COUNTED FALSE POSITIVE (the price of a syntactic summary): the callee
/// MENTIONS a secret it never writes and stores only a constant. The program
/// is safe — `sigil forge` outputs 5 bytes for any secret — yet the floor
/// rejects it, because the summary's label bound is every annotation reachable
/// from the callee, not the label that actually flows into a write. Main and
/// round 2 accept it. The raw-store anti-stub above
/// (`callee_that_stores_nothing_does_not_raise_the_callers_floor`) still holds:
/// a callee that writes NOTHING never raises the floor.
#[test]
fn callee_that_mentions_a_secret_but_writes_public_is_a_counted_false_positive() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let t: i64 @Secret = s + 1;\n\
         \x20   a[0] = 5;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "pinned COST: a secret-mentioning writer floors the caller even when it writes only \
         public bytes — if this flips to accepted, the summary became flow-precise"
    );
}

// ---------------------------------------------------------------------------
// S7 — THE ALIAS CHANNEL (round 3). A projected write labels the place's ROOT
// name, but aggregates are reference-semantic, so an alias taken BEFORE the
// write reads the value back. Found while probing the round-3 fix; verified
// END-TO-END with `sigil forge` on main at ae026aec and on round 2 (42 / 7
// bytes for the array and record forms). It is the intraprocedural twin of the
// S5 typed-write arm above: without S7 the same write made through a callee is
// rejected and made inline is accepted.
// ---------------------------------------------------------------------------

/// Array form: `b` aliases `a`; the secret written through `a` is read via `b`.
#[test]
fn alias_taken_before_a_secret_element_write_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let b: [i64; 2] = a;\n\
         \x20   a[0] = s;\n\
         \x20   return pub_sink(b[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a typed write must floor typed reads through every alias"
    );
}

/// Clean twin of the array alias form.
#[test]
fn alias_taken_before_a_public_element_write_is_clean() {
    let codes = module_code_set(
        "fn probe(k: i64 @Public) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let b: [i64; 2] = a;\n\
         \x20   a[0] = k;\n\
         \x20   return pub_sink(b[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public element write must not raise the floor; got {codes:?}"
    );
}

/// Record form: `q` aliases `r`.
#[test]
fn alias_taken_before_a_secret_field_write_is_t001() {
    let codes = module_code_set(
        "record Bag { n: i64, m: i64 }\n\
         fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut r: Bag = Bag { n: 0, m: 0 };\n\
         \x20   let q: Bag = r;\n\
         \x20   r.n = s;\n\
         \x20   return pub_sink(q.n);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a field write must floor typed reads through every alias"
    );
}

/// Clean twin of the record alias form.
#[test]
fn alias_taken_before_a_public_field_write_is_clean() {
    let codes = module_code_set(
        "record Bag { n: i64, m: i64 }\n\
         fn probe(k: i64 @Public) -> i64 @Public {\n\
         \x20   let mut r: Bag = Bag { n: 0, m: 0 };\n\
         \x20   let q: Bag = r;\n\
         \x20   r.n = k;\n\
         \x20   return pub_sink(q.n);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public field write must not raise the floor; got {codes:?}"
    );
}

/// The alias is read by a CALLEE: handing `b` over is itself a typed read of a
/// heap-resident local, so the floored label reaches the callee's parameter.
/// End-to-end repro (42 / 7 bytes on main and round 2).
#[test]
fn alias_handed_to_a_reader_after_a_secret_write_is_t001() {
    let codes = module_code_set(
        "fn get0(a: [i64; 2]) -> i64 @Public {\n\
         \x20   return a[0];\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let b: [i64; 2] = a;\n\
         \x20   a[0] = s;\n\
         \x20   return pub_sink(get0(b));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an alias handed to a reader after a secret write must be floored"
    );
}

/// Clean twin of the reader form.
#[test]
fn alias_handed_to_a_reader_after_a_public_write_is_clean() {
    let codes = module_code_set(
        "fn get0(a: [i64; 2]) -> i64 @Public {\n\
         \x20   return a[0];\n}\n\
         fn probe(k: i64 @Public) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let b: [i64; 2] = a;\n\
         \x20   a[0] = k;\n\
         \x20   return pub_sink(get0(b));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public write must not floor the reader's argument; got {codes:?}"
    );
}

/// S5 + S7 together: one callee writes the secret through `@Mut`, a SIBLING
/// callee reads it back. End-to-end repro (42 / 7 bytes on main and round 2).
#[test]
fn sibling_reader_after_a_callee_secret_write_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn get0(a: [i64; 2]) -> i64 @Public {\n\
         \x20   return a[0];\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(get0(a));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a sibling reader after a callee's secret write must be floored"
    );
}

/// Clean twin of the sibling-reader form.
#[test]
fn sibling_reader_after_a_callee_public_write_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn get0(a: [i64; 2]) -> i64 @Public {\n\
         \x20   return a[0];\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a);\n\
         \x20   return pub_sink(get0(a));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public-writing sibling must not raise the floor; got {codes:?}"
    );
}

// Round 3, second sweep: the other call and control shapes the typed-write
// floor must reach. Each was verified END-TO-END with `sigil forge` on main at
// ae026aec and on round 2 (42 / 7 bytes, all accepted) and is rejected by
// round 3; probe sources are the `x-*` files of the round-3 probe set.

/// A METHOD with `self @Mut` writes its own secret into the receiver: the
/// method call resolves to a named callee whose summary carries the write.
#[test]
fn method_with_mut_self_writing_its_own_secret_is_t001() {
    let codes = module_code_set(
        "record Bag { n: i64, m: i64 }\n\
         impl Bag {\n\
         \x20   pub fn poke(self: Bag @Mut) -> i64 @Public {\n\
         \x20       let s: i64 @Secret = 42;\n\
         \x20       self.n = s;\n\
         \x20       return 0;\n\
         \x20   }\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut b: Bag = Bag { n: 0, m: 0 };\n\
         \x20   let ignored: i64 = b.poke();\n\
         \x20   return pub_sink(b.n);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a `self @Mut` method's secret write must floor the caller's typed reads"
    );
}

/// Clean twin of the method form.
#[test]
fn method_with_mut_self_writing_a_public_value_is_clean() {
    let codes = module_code_set(
        "record Bag { n: i64, m: i64 }\n\
         impl Bag {\n\
         \x20   pub fn poke(self: Bag @Mut) -> i64 @Public {\n\
         \x20       let s: i64 = 42;\n\
         \x20       self.n = s;\n\
         \x20       return 0;\n\
         \x20   }\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut b: Bag = Bag { n: 0, m: 0 };\n\
         \x20   let ignored: i64 = b.poke();\n\
         \x20   return pub_sink(b.n);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public `self @Mut` write must not raise the floor; got {codes:?}"
    );
}

/// A GENERIC `@Mut` callee: the call resolves to a monomorph, whose summary
/// must carry the write (an unresolved name would take the program bound).
#[test]
fn generic_mut_callee_writing_its_own_secret_is_t001() {
    let codes = module_code_set(
        "fn poke<T>(a: [i64; 2] @Mut, t: T) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a, 1);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a generic callee's secret write must floor the caller's typed reads"
    );
}

/// Clean twin of the generic form.
#[test]
fn generic_mut_callee_writing_a_public_value_is_clean() {
    let codes = module_code_set(
        "fn poke<T>(a: [i64; 2] @Mut, t: T) -> i64 @Public {\n\
         \x20   let s: i64 = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let ignored: i64 = poke(a, 1);\n\
         \x20   return pub_sink(a[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a generic public writer must not raise the floor; got {codes:?}"
    );
}

/// LOOP-CARRIED callee write: the read at the top of the body precedes the
/// write in program text but follows it on the second iteration, so the floor
/// must ride the loop fixpoint.
#[test]
fn callee_secret_write_late_in_a_loop_floors_the_read_before_it_is_t001() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       r = pub_sink(a[0]);\n\
         \x20       let ignored: i64 = poke(a);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return r;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a loop-carried callee write must floor the read before it"
    );
}

/// Clean twin of the loop-carried callee form.
#[test]
fn callee_public_write_late_in_a_loop_is_clean() {
    let codes = module_code_set(
        "fn poke(a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let s: i64 = 42;\n\
         \x20   a[0] = s;\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       r = pub_sink(a[0]);\n\
         \x20       let ignored: i64 = poke(a);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return r;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a loop-carried public write must not raise the floor; got {codes:?}"
    );
}

/// LOOP-CARRIED alias write (S7 on the loop fixpoint).
#[test]
fn alias_secret_write_late_in_a_loop_floors_the_read_before_it_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let b: [i64; 2] = a;\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       r = pub_sink(b[0]);\n\
         \x20       a[0] = s;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return r;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a loop-carried alias write must floor the read before it"
    );
}

/// Clean twin of the loop-carried alias form.
#[test]
fn alias_public_write_late_in_a_loop_is_clean() {
    let codes = module_code_set(
        "fn probe(k: i64 @Public) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let b: [i64; 2] = a;\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       r = pub_sink(b[0]);\n\
         \x20       a[0] = k;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return r;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a loop-carried public write must not raise the floor; got {codes:?}"
    );
}

/// The alias is a record FIELD holding the array: `bx.data` shares `a`'s cell.
#[test]
fn alias_through_a_record_field_after_a_secret_write_is_t001() {
    let codes = module_code_set(
        "record Box { data: [i64; 2] }\n\
         fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let bx: Box = Box { data: a };\n\
         \x20   a[0] = s;\n\
         \x20   return pub_sink(bx.data[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a record-field alias read after a secret write must be floored"
    );
}

/// Clean twin of the record-field alias form.
#[test]
fn alias_through_a_record_field_after_a_public_write_is_clean() {
    let codes = module_code_set(
        "record Box { data: [i64; 2] }\n\
         fn probe(k: i64 @Public) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let bx: Box = Box { data: a };\n\
         \x20   a[0] = k;\n\
         \x20   return pub_sink(bx.data[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public write must not floor a record-field alias; got {codes:?}"
    );
}

/// COUNTED FALSE POSITIVE of S7 (alias-blindness): after a secret is written
/// into `a`, a read of an UNRELATED array `c` — which no write touched — is
/// floored too. Main and round 2 accept this program. An alias analysis would
/// remove the cost; the floors deliberately have none.
#[test]
fn secret_element_write_floors_an_unrelated_array_read_is_a_counted_false_positive() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let c: [i64; 2] = [3, 4];\n\
         \x20   a[0] = s;\n\
         \x20   return pub_sink(c[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "pinned COST: the alias-blind floor rejects a read no write touched — if this \
         flips to accepted, S7 became alias-precise (or was switched off)"
    );
}

// ---------------------------------------------------------------------------
// ROUND 4 — S8: the interprocedural LOAD direction, RESULT side. A callee that
// can raw-read memory (`load8`, `vec_load`, `str_from_raw` — the total
// `intrinsic_memory` classification, transitively over the call graph)
// returns a value joined with the CALLER's raw-load floor; an unnamed callee
// (indirect call, `grant` of a non-literal) returns both floors. Each closed
// channel was verified END-TO-END with `sigil forge` on main at ae026aec and
// on the round-3 CLI (accepted, bytes exfiltrated) before this round.
// ---------------------------------------------------------------------------

/// The round-3 review's FIRST blocker: `str_from_raw(p + 1, 32)` forges a
/// `str` over the host-written digest, and `byte_at(0)` reads it back at the
/// pointer's @Public label. `load8(p + 1)` in the same place was T001 since
/// round 1; the forge was not in the raw-read arm. Main, round 3: accepted,
/// `sigil forge` 227 bytes for input "" (sha256("")[0] = 0xe3), 62 for "b".
#[test]
fn str_from_raw_over_the_ffi_digest_is_t001() {
    let codes = string_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   let v: str = str_from_raw(p + 1, 32);\n\
         \x20   return pub_sink(v.byte_at(0));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a str view forged over host-written bytes must carry the post-FFI floor"
    );
}

/// Clean twin: the forge BEFORE the FFI views bytes the host has not written.
#[test]
fn str_from_raw_before_the_ffi_call_is_clean() {
    let codes = string_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let v: str = str_from_raw(p + 1, 32);\n\
         \x20   let early: i64 = pub_sink(v.byte_at(0));\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return early;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a forge before the FFI must stay clean; got {codes:?}"
    );
}

/// No FFI: `[s, 0]` materializes the secret into fresh cells, and a `str`
/// forged over the next 24 bytes dumps it (`2a` / `07` at byte 5 on main and
/// on round 3, 24 bytes of output).
#[test]
fn str_from_raw_over_a_secret_materialization_is_t001() {
    let codes = string_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let a: [i64; 2] @Secret = [s, 0];\n\
         \x20   let v: str = str_from_raw(b, 24);\n\
         \x20   return pub_sink(v.byte_at(5));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a str view forged after a secret materialization must be floored"
    );
}

/// Clean twin: a @Public materialization raises nothing, so the view is clean.
#[test]
fn str_from_raw_over_a_public_materialization_is_clean() {
    let codes = string_code_set(
        "fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc } {\n\
         \x20   let k: i64 = 42;\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let a: [i64; 2] = [k, 0];\n\
         \x20   let v: str = str_from_raw(b, 24);\n\
         \x20   return pub_sink(v.byte_at(5));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public materialization must not floor the forged view; got {codes:?}"
    );
}

/// The round-3 review's SAME HOLE THROUGH AN ORDINARY TOOL: a plain `module
/// tool; use sigil::string;` program calls the stdlib `str_from_bytes` over
/// the bytes its own `[s, 0]` left behind. The callee's summary was
/// `writes_memory` at a @Public annotation and its own floors start clean, so
/// nothing rose; the result was built from memory the CALLER's floor labels.
/// Main and round 3 (composed with the real stdlib as the bench harness
/// does): accepted, `sigil forge` 42 / 7 bytes. S8 joins the caller's
/// raw-load floor into the result of a raw-reading callee.
#[test]
fn stdlib_from_bytes_over_a_secret_materialization_is_t001() {
    let codes = composed_code_set(
        "fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let a: [i64; 2] @Secret = [s, 0];\n\
         \x20   let r: Option<str> = str_from_bytes(b, 13);\n\
         \x20   match r {\n\
         \x20       Some(v) => { return pub_sink(v.byte_at(5)); },\n\
         \x20       None => { return 0; }\n\
         \x20   }\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   return probe();\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a stdlib callee that raw-reads the caller's dirty bytes must return the caller's floor"
    );
}

/// Clean twin of the stdlib route: with a @Public materialization the
/// caller's floor is clean and the composed program stays accepted.
#[test]
fn stdlib_from_bytes_over_a_public_materialization_is_clean() {
    let codes = composed_code_set(
        "fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let k: i64 = 42;\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let a: [i64; 2] = [k, 0];\n\
         \x20   let r: Option<str> = str_from_bytes(b, 13);\n\
         \x20   match r {\n\
         \x20       Some(v) => { return pub_sink(v.byte_at(5)); },\n\
         \x20       None => { return 0; }\n\
         \x20   }\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   return probe();\n}\n",
    );
    assert!(
        codes.is_empty(),
        "the stdlib route over public bytes must stay accepted; got {codes:?}"
    );
}

/// A callee that raw-reads and STORES what it read into a `@Mut` argument
/// hands the caller the floored bytes through a typed read: the caller's
/// floor joins the site taint its writes are floored at, so `out[0]` is T001.
/// The FFI is the floor source here because S1 raises `raw_load` ALONE — a
/// secret raw store would raise the typed-read floor too (S4) and reject
/// `out[0]` without S8's help (that is what a mutation of S8 showed).
#[test]
fn callee_storing_a_raw_read_into_a_mut_argument_after_callers_ffi_is_t001() {
    let codes = tool_code_set(
        "fn peek_into(p: i64, out: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   out[0] = load8(p + 1);\n\
         \x20   return 0;\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let mut out: [i64; 2] = [0, 0];\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   let ignored: i64 = peek_into(p, out);\n\
         \x20   return pub_sink(out[0]);\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a raw read the callee stores for the caller must be floored at the caller's label"
    );
}

/// COUNTED FALSE POSITIVE of S8 (address-blindness): the callee reads a
/// pointer the caller minted BEFORE the FFI and only ever wrote a public
/// byte through — the host wrote elsewhere — but the raw-load floor is per
/// function, not per cell, so the result is floored. Main accepts this
/// program, and without S8 (mutation-checked) so does this branch: the FFI
/// raises `raw_load` alone, so nothing but S8 reaches `rd`'s result.
#[test]
fn callee_raw_read_of_an_unrelated_clean_pointer_after_callers_ffi_is_a_counted_false_positive() {
    let codes = tool_code_set(
        "fn rd(p: i64) -> i64 @Public {\n\
         \x20   return load8(p);\n}\n\
         fn probe(input_ptr: i32, input_len: i32) -> i64 @Public ! { Alloc, FFI, Unsafe } {\n\
         \x20   let q: i64 = alloc(1);\n\
         \x20   store8(q, 1);\n\
         \x20   let unused: i64 @Internal = crypto_sha256(input_ptr, input_len);\n\
         \x20   return pub_sink(rd(q));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "pinned COST: the address-blind floor rejects a read of a clean cell — if this \
         flips to accepted, S8 became address-precise (or was switched off)"
    );
}

// ---------------------------------------------------------------------------
// ROUND 4 — the MATERIALIZATION channel of S5: a callee that only BUILDS a
// secret aggregate (no store at an existing address) was not `writes_memory`
// in the scan, so the caller's next raw load read the fresh cells at a clean
// floor. `[s, 0]` in the callee, `load8(b + i)` in the caller: main and
// round 3 dumped `2a` / `07` at byte 5 of 48. The scan now notes every
// heap-resident value the way the intraprocedural S2 choke point does.
// ---------------------------------------------------------------------------

/// The callee builds `[s, 0]` and returns 0; the caller's raw load through a
/// pointer minted before the call reads the secret back.
#[test]
fn callee_that_only_materializes_a_secret_aggregate_floors_the_callers_raw_load_is_t001() {
    let codes = module_code_set(
        "fn mk() -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let a: [i64; 2] @Secret = [s, 0];\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let z: i64 = mk();\n\
         \x20   return pub_sink(load8(b + 5));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's secret materialization must floor the caller's raw loads"
    );
}

/// Clean twin: a callee that builds a @Public aggregate raises nothing.
#[test]
fn callee_that_only_materializes_a_public_aggregate_is_clean() {
    let codes = module_code_set(
        "fn mk() -> i64 @Public {\n\
         \x20   let k: i64 = 42;\n\
         \x20   let a: [i64; 2] = [k, 0];\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   let z: i64 = mk();\n\
         \x20   return pub_sink(load8(b + 5));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public materialization in a callee must not raise the floor; got {codes:?}"
    );
}

/// Fence: a materializing callee raises the RAW-load floor only (fresh cells
/// overlap no live typed value — S2's argument), so the caller's typed reads
/// stay clean.
#[test]
fn callee_that_only_materializes_a_secret_aggregate_does_not_floor_typed_reads() {
    let codes = module_code_set(
        "fn mk() -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 42;\n\
         \x20   let a: [i64; 2] @Secret = [s, 0];\n\
         \x20   return 0;\n}\n\
         fn probe() -> i64 @Public ! { Alloc } {\n\
         \x20   let c: [i64; 2] = [3, 4];\n\
         \x20   let z: i64 = mk();\n\
         \x20   return pub_sink(c[0]);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a materialization floors raw loads only, never typed reads; got {codes:?}"
    );
}

// ---------------------------------------------------------------------------
// ROUND 4 — S9: a closure body's floors flow back to its construct site, and a
// `grant` of anything but a closure literal takes the program-wide bound.
// The round-3 review's SECOND blocker (a): `grant(&f, fn(c) { a[0] = s; })`
// then `a[0]` was accepted on main and round 3 — the Grant arm checked the
// body in a `closure_env` whose floors never flowed back, and the scan saw a
// `ClosureConstruct` as inert. Actors do not `forge`, so these are static
// pins; the IndirectCall twin was already T001 on round 3.
// ---------------------------------------------------------------------------

/// The grant-invoked closure mints a secret and writes it into a captured
/// aggregate; the handler reads it back. This is THE pin that depends on S9
/// (measured: with `HEAP_FLOOR_CLOSURE_FLOWS_BACK = false` and nothing else
/// changed, this file's 104 round-4 tests went 103 / 1 — exactly this one),
/// so it branches on the switch the way the S3 pins do instead of pinning
/// the switch at compile time: S9 can be measured off without this binary
/// failing to build.
#[test]
fn grant_closure_writing_its_own_secret_into_a_capture_is_t001() {
    let codes = plain_code_set(
        "cap type Fuel {}\n\
         entry actor Main {\n\
         \x20   state { f: Fuel }\n\
         \x20   on Go() -> i64 {\n\
         \x20       let mut a: [i64; 2] = [0, 0];\n\
         \x20       let r: i64 = grant(&f, fn(c: &Fuel) -> i64 { let s: i64 @Secret = 42; a[0] = s; return 0; });\n\
         \x20       return pub_sink(a[0]);\n\
         \x20   }\n}\n",
    );
    if HEAP_FLOOR_CLOSURE_FLOWS_BACK {
        assert_eq!(
            codes,
            set(&["T001"]),
            "a grant-invoked closure's secret write must floor the site's typed reads"
        );
    } else {
        assert!(
            codes.is_empty(),
            "S9 OFF is the round-3 hole: the grant body's floors die with its env and \
             the handler's `a[0]` is accepted — measured, not wanted; got {codes:?}"
        );
    }
}

/// Clean twin: the grant-invoked closure writes a @Public value.
#[test]
fn grant_closure_writing_a_public_value_into_a_capture_is_clean() {
    let codes = plain_code_set(
        "cap type Fuel {}\n\
         entry actor Main {\n\
         \x20   state { f: Fuel }\n\
         \x20   on Go() -> i64 {\n\
         \x20       let mut a: [i64; 2] = [0, 0];\n\
         \x20       let r: i64 = grant(&f, fn(c: &Fuel) -> i64 { let k: i64 = 42; a[0] = k; return 0; });\n\
         \x20       return pub_sink(a[0]);\n\
         \x20   }\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public write inside a grant closure must not raise the floor; got {codes:?}"
    );
}

/// The IndirectCall twin the round-3 review used as its control: the same
/// closure bound to a local and called — T001 since round 3, still T001.
#[test]
fn stored_closure_writing_its_own_secret_into_a_capture_is_t001() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   on Go() -> i64 {\n\
         \x20       let mut a: [i64; 2] = [0, 0];\n\
         \x20       let g = fn(c: i64) -> i64 { let s: i64 @Secret = 42; a[0] = s; return 0; };\n\
         \x20       let r: i64 = g(0);\n\
         \x20       return pub_sink(a[0]);\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a stored closure's secret write must floor the site's typed reads"
    );
}

/// A closure that writes its own secret into a capture is a memory write in
/// the enclosing function's S5 SUMMARY too (the construct site is a call
/// edge to the lifted body), so a CALLER of that function is floored.
#[test]
fn callee_whose_grant_closure_writes_a_secret_floors_its_caller_is_t001() {
    let codes = plain_code_set(
        "cap type Fuel {}\n\
         fn poke(f: &Fuel, a: [i64; 2] @Mut) -> i64 @Public {\n\
         \x20   let r: i64 = grant(f, fn(c: &Fuel) -> i64 { let s: i64 @Secret = 42; a[0] = s; return 0; });\n\
         \x20   return 0;\n}\n\
         entry actor Main {\n\
         \x20   state { f: Fuel }\n\
         \x20   on Go() -> i64 {\n\
         \x20       let mut a: [i64; 2] = [0, 0];\n\
         \x20       let r: i64 = poke(&f, a);\n\
         \x20       return pub_sink(a[0]);\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a grant closure's write must appear in the enclosing function's summary"
    );
}

// ---------------------------------------------------------------------------
// ROUND 4 — S10: the actor dispatch loop. The `while`/`for` fixpoints carry
// the floors across iterations, but persistent `mut` state re-entered per
// message carried nothing: the round-3 review's SECOND blocker (b). Every
// `init`/handler of an actor now starts at the fixpoint of what all of them
// leave in the state heap, and every state-field read (scalar too) is a
// typed memory read. Actors do not `forge`, so these are static pins; the
// corpus cost is measured (2 tool actors carry state at all).
// ---------------------------------------------------------------------------

/// ONE handler: reads `buf[0]` FIRST, then writes `buf[s & 1] = 1` under a
/// condition. Dispatch 2 reads what dispatch 1 wrote. Accepted on main and
/// round 3.
#[test]
fn handler_reading_state_before_its_own_secret_index_write_is_t001() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut buf: [i64; 2] }\n\
         \x20   init() { buf = [0, 0]; }\n\
         \x20   on Step(x: i64) -> i64 {\n\
         \x20       let r: i64 = pub_sink(buf[0]);\n\
         \x20       if x == 0 {\n\
         \x20           let s: i64 @Secret = 41;\n\
         \x20           buf[s & 1] = 1;\n\
         \x20       } else {\n\
         \x20       }\n\
         \x20       return r;\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a state read before a later dispatch's secret write must be floored"
    );
}

/// Clean twin: the same handler with a @Public index.
#[test]
fn handler_reading_state_before_its_own_public_index_write_is_clean() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut buf: [i64; 2] }\n\
         \x20   init() { buf = [0, 0]; }\n\
         \x20   on Step(x: i64) -> i64 {\n\
         \x20       let r: i64 = pub_sink(buf[0]);\n\
         \x20       if x == 0 {\n\
         \x20           let k: i64 = 41;\n\
         \x20           buf[k & 1] = 1;\n\
         \x20       } else {\n\
         \x20       }\n\
         \x20       return r;\n\
         \x20   }\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public state write must not floor the actor; got {codes:?}"
    );
}

/// TWO handlers, typed: `Put` writes at a secret index, `Get` reads.
#[test]
fn handler_reading_state_another_handler_wrote_at_a_secret_index_is_t001() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut buf: [i64; 2] }\n\
         \x20   init() { buf = [0, 0]; }\n\
         \x20   on Put(s: i64 @Secret) -> i64 {\n\
         \x20       buf[s & 1] = 1;\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(buf[0]);\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a cross-handler secret index write must floor the reading handler"
    );
}

/// Clean twin of the two-handler typed form.
#[test]
fn handler_reading_state_another_handler_wrote_at_a_public_index_is_clean() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut buf: [i64; 2] }\n\
         \x20   init() { buf = [0, 0]; }\n\
         \x20   on Put(k: i64 @Public) -> i64 {\n\
         \x20       buf[k & 1] = 1;\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(buf[0]);\n\
         \x20   }\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public cross-handler write must not floor the actor; got {codes:?}"
    );
}

/// TWO handlers, raw: `Put` raw-stores the secret, `Get` raw-loads it.
#[test]
fn handler_raw_loading_what_another_handler_raw_stored_is_t001() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   on Put(s: i64 @Secret) -> i64 {\n\
         \x20       store8(4096, s);\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(load8(4096));\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a cross-handler raw store must floor the reading handler's raw loads"
    );
}

/// Clean twin of the raw two-handler form.
#[test]
fn handler_raw_loading_what_another_handler_raw_stored_publicly_is_clean() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   on Put(k: i64 @Public) -> i64 {\n\
         \x20       store8(4096, k);\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(load8(4096));\n\
         \x20   }\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public cross-handler raw store must not floor the actor; got {codes:?}"
    );
}

/// A SCALAR state cell is memory too: `Put` raw-stores a secret at an
/// address the checker never verified, and `Get` reads `count` — a cell
/// behind the state pointer, not a wasm local. Accepted on main and round 3
/// (scalar state reads were not typed memory reads).
#[test]
fn handler_reading_a_scalar_state_field_after_another_handlers_secret_raw_store_is_t001() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut count: i64 }\n\
         \x20   init() { count = 0; }\n\
         \x20   on Put(s: i64 @Secret) -> i64 {\n\
         \x20       store8(4096, s);\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(count);\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a scalar state read after a cross-handler secret raw store must be floored"
    );
}

/// Clean twin: a scalar state field read in an actor whose handlers write
/// nothing non-@Public stays clean (the common counter shape).
#[test]
fn handler_reading_a_scalar_state_field_in_a_public_actor_is_clean() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut count: i64 }\n\
         \x20   init() { count = 0; }\n\
         \x20   on Bump() -> i64 {\n\
         \x20       count = count + 1;\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(count);\n\
         \x20   }\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public counter actor must stay clean; got {codes:?}"
    );
}

/// Fence: a handler that takes a @Secret PARAMETER but writes nothing
/// non-@Public into memory does not floor the actor — S10 is keyed on what
/// the handlers WRITE, not on a secret anywhere in the actor.
#[test]
fn handler_with_a_secret_parameter_that_writes_nothing_secret_is_clean() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut count: i64 }\n\
         \x20   init() { count = 0; }\n\
         \x20   on Put(s: i64 @Secret) -> i64 {\n\
         \x20       count = count + 1;\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(count);\n\
         \x20   }\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a secret parameter that never reaches memory must not floor the actor; got {codes:?}"
    );
}

/// COUNTED FALSE POSITIVE of S10 (per-actor, not per-cell): `Put` writes a
/// secret into `buf`; `Get` reads the UNRELATED state field `other`, which no
/// handler ever writes non-publicly — floored anyway. Main and round 3 accept.
#[test]
fn secret_state_write_floors_an_unrelated_state_field_read_is_a_counted_false_positive() {
    let codes = plain_code_set(
        "entry actor Main {\n\
         \x20   state { mut buf: [i64; 2], mut other: [i64; 2] }\n\
         \x20   init() { buf = [0, 0]; other = [3, 4]; }\n\
         \x20   on Put(s: i64 @Secret) -> i64 {\n\
         \x20       buf[s & 1] = 1;\n\
         \x20       return 0;\n\
         \x20   }\n\
         \x20   on Get() -> i64 {\n\
         \x20       return pub_sink(other[0]);\n\
         \x20   }\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "pinned COST: the per-actor floor rejects a read of a field no secret write \
         touched — if this flips to accepted, S10 became per-cell (or was switched off)"
    );
}

// ---------------------------------------------------------------------------
// ROUND 4 — the memory-class CENSUS. `intrinsic_memory` is total over
// `TypedIntrinsicKind` (a new variant fails to compile), and this test pins
// WHICH class every variant carries by parsing the enum and the match, so a
// reclassification — or a variant added to the enum and the match together
// with a wrong class — is review content here, not a silent join. SC-P4: the
// two anti-stubs below plant a variant and a reclassification and show the
// detector catches both.
// ---------------------------------------------------------------------------

/// The pinned classification: every variant of `TypedIntrinsicKind`, once.
const INTRINSIC_MEMORY_PINS: &[(&str, &str)] = &[
    ("Alloc", "Inert"),
    ("Load8", "RawRead"),
    ("Store8", "RawWrite"),
    ("U256FromI64", "Inert"),
    ("U256Make", "Inert"),
    ("U256Limb", "Inert"),
    ("TrapIf", "Inert"),
    ("Trap", "Inert"),
    ("SlotNew", "Inert"),
    ("SlotPut", "CheckedWrite"),
    ("SlotTake", "CheckedWrite"),
    ("ArrayLen", "Inert"),
    ("SliceLen", "Inert"),
    ("ArrayIsEmpty", "Inert"),
    ("SliceIsEmpty", "Inert"),
    ("ArrayContains", "Inert"),
    ("SliceContains", "Inert"),
    ("SliceFirst", "Inert"),
    ("SliceLast", "Inert"),
    ("StrLen", "Inert"),
    ("StrAsOutput", "Inert"),
    ("StrIsEmpty", "Inert"),
    ("StrByteAt", "Inert"),
    ("IntConvert", "Inert"),
    ("StrSubstr", "Inert"),
    ("StrFromRaw", "RawRead"),
    ("CtEq", "Inert"),
    ("CtSelect", "Inert"),
    ("CtLt", "Inert"),
    ("VecStore", "RawWrite"),
    ("VecLoad", "RawRead"),
];

fn compiler_src(file: &str) -> String {
    let path = format!("{}/src/{file}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("census cannot read {path}: {e}"))
}

/// The variant names of `pub enum TypedIntrinsicKind` in `src`: the block
/// from its opening brace to the first `}` at column zero, one variant per
/// four-space-indented line that starts with a capitalized identifier.
fn intrinsic_enum_variants(src: &str) -> BTreeSet<String> {
    let start = src
        .find("pub enum TypedIntrinsicKind {")
        .expect("typed_ast.rs declares `pub enum TypedIntrinsicKind {`");
    let body = &src[start..];
    let end = body.find("\n}\n").expect("the enum closes at column zero");
    body[..end]
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("    ")?;
            if rest.starts_with(' ') || rest.starts_with('/') {
                return None;
            }
            let name: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect();
            (name.chars().next().is_some_and(|c| c.is_ascii_uppercase())).then_some(name)
        })
        .collect()
}

/// The classification `fn intrinsic_memory` makes in `src`: every
/// `TypedIntrinsicKind::<Name>` pattern maps to the `IntrinsicMemory::<Class>`
/// that ends its arm. Comment lines are skipped, so a `::`-qualified name in
/// a comment inside the function would be a parse hazard — the function's
/// doc says to keep them out.
fn intrinsic_memory_classes(src: &str) -> BTreeMap<String, String> {
    let start = src
        .find("pub fn intrinsic_memory(")
        .expect("taint_check.rs declares `pub fn intrinsic_memory(`");
    let body = &src[start..];
    let end = body
        .find("\n}\n")
        .expect("the function closes at column zero");
    let mut classes = BTreeMap::new();
    let mut pending: Vec<String> = Vec::new();
    for line in body[..end].lines() {
        if line.trim_start().starts_with("//") {
            continue;
        }
        let mut rest = line;
        while let Some(at) = rest.find("TypedIntrinsicKind::") {
            let after = &rest[at + "TypedIntrinsicKind::".len()..];
            let name: String = after
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect();
            pending.push(name);
            rest = after;
        }
        if let Some(at) = line.find("IntrinsicMemory::") {
            let class: String = line[at + "IntrinsicMemory::".len()..]
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric())
                .collect();
            for name in pending.drain(..) {
                let previous = classes.insert(name.clone(), class.clone());
                assert!(
                    previous.is_none(),
                    "variant `{name}` appears in two arms of `intrinsic_memory`"
                );
            }
        }
    }
    assert!(
        pending.is_empty(),
        "patterns with no class after them: {pending:?}"
    );
    classes
}

/// The census proper: enum variants == pinned names == classified names, and
/// every pinned class is the class the match makes.
fn census_mismatches(enum_src: &str, match_src: &str) -> Vec<String> {
    let variants = intrinsic_enum_variants(enum_src);
    let classes = intrinsic_memory_classes(match_src);
    let pinned: BTreeMap<&str, &str> = INTRINSIC_MEMORY_PINS.iter().copied().collect();
    let mut problems = Vec::new();
    for v in &variants {
        if !pinned.contains_key(v.as_str()) {
            problems.push(format!(
                "enum variant `{v}` has no pin in INTRINSIC_MEMORY_PINS"
            ));
        }
        if !classes.contains_key(v) {
            problems.push(format!(
                "enum variant `{v}` is not classified by intrinsic_memory"
            ));
        }
    }
    for (name, class) in &pinned {
        if !variants.contains(*name) {
            problems.push(format!("pin `{name}` names no enum variant"));
        }
        match classes.get(*name) {
            Some(actual) if actual == class => {}
            Some(actual) => problems.push(format!(
                "`{name}` is pinned {class} but intrinsic_memory says {actual}"
            )),
            None => {}
        }
    }
    problems
}

#[test]
fn intrinsic_memory_census_is_total() {
    let enum_src = compiler_src("typed_ast.rs");
    let match_src = compiler_src("taint_check.rs");
    assert_eq!(
        INTRINSIC_MEMORY_PINS.len(),
        intrinsic_enum_variants(&enum_src).len(),
        "one pin per enum variant"
    );
    let problems = census_mismatches(&enum_src, &match_src);
    assert!(
        problems.is_empty(),
        "intrinsic memory census drifted:\n{}",
        problems.join("\n")
    );
}

/// ANTI-STUB (SC-P4): a variant planted in the enum text is reported as
/// unpinned and unclassified — the detector sees what it claims to see.
#[test]
fn intrinsic_memory_census_detects_a_planted_variant() {
    let enum_src = compiler_src("typed_ast.rs");
    let match_src = compiler_src("taint_check.rs");
    let planted = enum_src.replacen(
        "pub enum TypedIntrinsicKind {\n",
        "pub enum TypedIntrinsicKind {\n    PlantedLoad,\n",
        1,
    );
    assert_ne!(planted, enum_src, "the plant must land");
    let problems = census_mismatches(&planted, &match_src);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("`PlantedLoad` has no pin"))
            && problems
                .iter()
                .any(|p| p.contains("`PlantedLoad` is not classified")),
        "the census must report the planted variant twice; got {problems:?}"
    );
}

/// ANTI-STUB (SC-P4): a reclassification planted in the match text — the
/// raw-read arm rewritten as inert — is reported against the pins.
#[test]
fn intrinsic_memory_census_detects_a_planted_reclassification() {
    let enum_src = compiler_src("typed_ast.rs");
    let match_src = compiler_src("taint_check.rs");
    let planted = match_src.replacen(
        "| TypedIntrinsicKind::StrFromRaw { .. } => IntrinsicMemory::RawRead,",
        "| TypedIntrinsicKind::StrFromRaw { .. } => IntrinsicMemory::Inert,",
        1,
    );
    assert_ne!(planted, match_src, "the plant must land");
    let problems = census_mismatches(&enum_src, &planted);
    assert!(
        problems
            .iter()
            .any(|p| p.contains("`StrFromRaw` is pinned RawRead but intrinsic_memory says Inert"))
            && problems
                .iter()
                .any(|p| p.contains("`Load8` is pinned RawRead but intrinsic_memory says Inert")),
        "the census must report the reclassified arm; got {problems:?}"
    );
}

// ---------------------------------------------------------------------------
// ROUND 5 — S11: SHARED STATIC DATA. `wasm.rs::collect_static_data` interns
// every distinct string literal ONCE from offset 1024 (deduped by value); a use
// allocates only an 8-byte header pointing at the shared bytes, which are
// ordinary writable linear memory. The round-4 review's blocker: a NAMED callee
// that reads a literal (`"AAAAAAAA".byte_at(3)`) returned the caller's
// raw-stored secret as @Public — `sigil forge` printed 2a / 07 on main AND on
// round 4, in a plain `module tool;` with no FFI — because S8 assumed a named
// callee's typed reads reach only its own fresh cells. Probing that found the
// same class inside ONE function (two literals compared after the store leak
// the bit: 00 / 01 on both binaries) and through an f-string (2a on both).
// Every end-to-end repro below binds its secret with `let s: i64 @Secret = n`
// in a plain tool; the tests take it as a parameter — the same label.
// ---------------------------------------------------------------------------

/// The round-4 review's repro (r5): the caller raw-stores its secret at the
/// literal's own address (`as_output() >> 32` is the data pointer) and a
/// named callee that materializes the SAME literal reads it back.
#[test]
fn named_callee_reading_a_string_literal_after_a_secret_store_into_it_is_t001() {
    let codes = module_code_set(
        "fn peek() -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   return l.byte_at(3);\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   let addr: i64 = l.as_output() >> 32;\n\
         \x20   store8(addr + 3, s);\n\
         \x20   return pub_sink(peek());\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "a named callee's literal read is a read of the caller's floored memory",
    );
}

/// The review's r5b: the caller holds NO literal and needs no address oracle —
/// static data starts at the constant 1024, so `store8(1024 + 3, s)` lands in
/// the callee's literal. `sigil forge` printed 2a on main and round 4.
#[test]
fn named_callee_reading_a_string_literal_after_a_secret_store_at_the_static_base_is_t001() {
    let codes = module_code_set(
        "fn peek() -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   return l.byte_at(3);\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   store8(1024 + 3, s);\n\
         \x20   return pub_sink(peek());\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "the static base is a constant: no literal in the caller is needed",
    );
}

/// Clean twin: the same program storing a @Public value into the literal.
#[test]
fn named_callee_reading_a_string_literal_after_a_public_store_into_it_is_clean() {
    let codes = module_code_set(
        "fn peek() -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   return l.byte_at(3);\n}\n\
         fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   let addr: i64 = l.as_output() >> 32;\n\
         \x20   store8(addr + 3, k);\n\
         \x20   return pub_sink(peek());\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store raises no floor, so the callee's literal read is clean; got {codes:?}"
    );
}

/// Flow-sensitivity fence: the callee reads the literal BEFORE the secret
/// store, so its result was built from bytes no store had touched.
#[test]
fn named_callee_reading_a_string_literal_before_the_secret_store_is_clean() {
    let codes = module_code_set(
        "fn peek() -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   return l.byte_at(3);\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let k: i64 = peek();\n\
         \x20   store8(1024 + 3, s);\n\
         \x20   return pub_sink(k);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a call before the store is at a clean floor; got {codes:?}"
    );
}

/// The intraprocedural form found while probing the fix: neither operand of
/// `"AAAAAAAA" == "AAABAAAA"` was a typed read, so a raw store of the secret's
/// low bit into one literal's byte 3 flipped the comparison and `sigil forge`
/// printed 00 / 01 on main and round 4. A `str` literal is now a typed read.
#[test]
fn two_string_literals_compared_after_a_secret_store_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   store8((l.as_output() >> 32) + 3, 65 + (s & 1));\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   if \"AAAAAAAA\" == \"AAABAAAA\" {\n\
         \x20       r = 1;\n\
         \x20   }\n\
         \x20   return pub_sink(r);\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "a literal is a typed read of shared memory: the compare is floored",
    );
}

/// Clean twin of the compare: a @Public byte is stored into the literal.
#[test]
fn two_string_literals_compared_after_a_public_store_is_clean() {
    let codes = module_code_set(
        "fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   store8((l.as_output() >> 32) + 3, 65 + (k & 1));\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   if \"AAAAAAAA\" == \"AAABAAAA\" {\n\
         \x20       r = 1;\n\
         \x20   }\n\
         \x20   return pub_sink(r);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "literals alone raise nothing; got {codes:?}"
    );
}

/// The same compare inside a named callee: `sigil forge` printed 01 for the
/// bit on main and round 4; the callee's literal reads make it `reads_typed`.
#[test]
fn named_callee_comparing_two_string_literals_after_a_secret_store_is_t001() {
    let codes = module_code_set(
        "fn same() -> i64 @Public {\n\
         \x20   if \"AAAAAAAA\" == \"AAABAAAA\" {\n\
         \x20       return 1;\n\
         \x20   }\n\
         \x20   return 0;\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = \"AAAAAAAA\";\n\
         \x20   store8((l.as_output() >> 32) + 3, 65 + (s & 1));\n\
         \x20   return pub_sink(same());\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "a callee that only compares literals still reads shared static data",
    );
}

/// An f-string's chunks are string literals (`air.rs` lowers each to a
/// `Literal::Str` before the `str_concat` chain), so they are shared static
/// data too: `sigil forge` printed 2a through this callee on main and round 4.
#[test]
fn named_callee_reading_an_f_string_after_a_secret_store_is_t001() {
    let codes = module_code_set(
        "fn peek() -> i64 @Public ! { Alloc } {\n\
         \x20   let l: str = f\"AAAAAAAA\";\n\
         \x20   return l.byte_at(3);\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   store8(1024 + 3, s);\n\
         \x20   return pub_sink(peek());\n}\n",
    );
    assert_t001_when_s11_on(&codes, "an f-string is a typed read of shared static data");
}

// The two `T001` pins below (with their twins) are the ONLY pins of the
// `FString(_)` arm of `reads_typed_memory`: an f-string's literal chunks are raw `String`s inside
// `TypedFStringPart::Literal`, not child expressions, so no other arm floors
// them — the f-string callee test above passes through `byte_at` (an
// intrinsic) whether or not that arm exists (the round-5 review's blocker:
// the arm mutated to `false` left this file green). Every static read in each
// program is an f-string; the store goes to the static base constant so no
// `str` literal is materialized anywhere in the probe.
//
// These six compile under the inner-ring `PLAIN_HDR`, not `MOD_HDR`: a
// two-chunk f-string compare lowers through `string::str_join` (inner ring),
// whose `Vec` instances are filed under the program's first module, so in an
// outer-ring module the emission gate refuses the program with exactly
// {R007} whatever the taint verdict (#768; measured at the group-4 landing on
// all four clean twins, the two leaks staying {T001} under both headers).
// The ring is incidental to what these pins measure — the f-string arm of
// the S11 floor — so they sit where the emission gate is silent.

/// The review's y1: `if f"AAAAAAAA" == f"AAABAAAA"` after a raw store of the
/// secret's low bit into static data flips the comparison — `sigil forge`
/// printed 00 / 01 for the bit on main at ae026aec (`check` clean), the same
/// leak as the `str` literal compare, reached through the f-string arm alone.
#[test]
fn f_string_compare_after_a_secret_store_is_t001() {
    let codes = plain_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   store8(1024 + 3, 65 + (s & 1));\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   if f\"AAAAAAAA\" == f\"AAABAAAA\" {\n\
         \x20       r = 1;\n\
         \x20   }\n\
         \x20   return pub_sink(r);\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "an f-string's chunks are shared static data: the compare is a floored typed read",
    );
}

/// Clean twin of y1: a @Public byte is stored into static data, so no floor
/// rises and the f-string compare is accepted.
#[test]
fn f_string_compare_after_a_public_store_is_clean() {
    let codes = plain_code_set(
        "fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   store8(1024 + 3, 65 + (k & 1));\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   if f\"AAAAAAAA\" == f\"AAABAAAA\" {\n\
         \x20       r = 1;\n\
         \x20   }\n\
         \x20   return pub_sink(r);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "f-strings alone raise nothing; got {codes:?}"
    );
}

/// Flow-sensitivity fence for y1: the f-string compare happens BEFORE the
/// secret store, so it read bytes no store had touched.
#[test]
fn f_string_compare_before_the_secret_store_is_clean() {
    let codes = plain_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut r: i64 = 0;\n\
         \x20   if f\"AAAAAAAA\" == f\"AAABAAAA\" {\n\
         \x20       r = 1;\n\
         \x20   }\n\
         \x20   store8(1024 + 3, 65 + (s & 1));\n\
         \x20   return pub_sink(r);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a read before the store is at a clean floor; got {codes:?}"
    );
}

/// The review's y2: the same f-string compare inside a NAMED callee — `sigil
/// forge` printed 01 for the bit on main at ae026aec. The callee's only typed
/// reads are the two f-strings, so it is `reads_typed` through the f-string
/// arm alone and its result joins the caller's typed-read floor.
#[test]
fn named_callee_comparing_two_f_strings_after_a_secret_store_is_t001() {
    let codes = plain_code_set(
        "fn same() -> i64 @Public {\n\
         \x20   if f\"AAAAAAAA\" == f\"AAABAAAA\" {\n\
         \x20       return 1;\n\
         \x20   }\n\
         \x20   return 0;\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   store8(1024 + 3, 65 + (s & 1));\n\
         \x20   return pub_sink(same());\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "a callee whose only typed reads are f-strings still reads shared static data",
    );
}

/// Clean twin of y2: the caller stores a @Public byte, so the callee's
/// f-string reads are at a clean floor.
#[test]
fn named_callee_comparing_two_f_strings_after_a_public_store_is_clean() {
    let codes = plain_code_set(
        "fn same() -> i64 @Public {\n\
         \x20   if f\"AAAAAAAA\" == f\"AAABAAAA\" {\n\
         \x20       return 1;\n\
         \x20   }\n\
         \x20   return 0;\n}\n\
         fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   store8(1024 + 3, 65 + (k & 1));\n\
         \x20   return pub_sink(same());\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store raises no floor for the callee's f-string reads; got {codes:?}"
    );
}

/// Flow-sensitivity fence for y2: the callee runs BEFORE the secret store.
#[test]
fn named_callee_comparing_two_f_strings_before_the_secret_store_is_clean() {
    let codes = plain_code_set(
        "fn same() -> i64 @Public {\n\
         \x20   if f\"AAAAAAAA\" == f\"AAABAAAA\" {\n\
         \x20       return 1;\n\
         \x20   }\n\
         \x20   return 0;\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let k: i64 = same();\n\
         \x20   store8(1024 + 3, 65 + (s & 1));\n\
         \x20   return pub_sink(k);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a call before the store is at a clean floor; got {codes:?}"
    );
}

/// COUNTED COST of dropping the premise: the callee reads its OWN fresh array,
/// which the caller's raw store provably did not reach, yet its result is
/// floored — S11 is address-blind by choice (the checker cannot bound a raw
/// store's address, so it cannot tell a fresh cell from static data). main at
/// ae026aec and round 4 accept this program (`sigil forge` prints 05).
#[test]
fn named_callee_reading_its_own_fresh_array_after_callers_secret_store_is_a_counted_false_positive()
{
    let codes = module_code_set(
        "fn own() -> i64 @Public ! { Alloc } {\n\
         \x20   let a: [i64; 2] = [5, 6];\n\
         \x20   return a[0];\n}\n\
         fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   store8(p, s);\n\
         \x20   return pub_sink(own());\n}\n",
    );
    assert_t001_when_s11_on(
        &codes,
        "the coarse rule floors every typed-reading callee: a counted cost, not a claim",
    );
}

// ---------------------------------------------------------------------------
// STILL OPEN after round 5 — each pinned as an ACCEPT with its EXACT (empty)
// code set, and each verified END-TO-END with `sigil forge` on this round's CLI
// AND on main at ae026aec. They are the interprocedural LOAD direction's
// SINK-INSIDE-callee form (S3, off) and the allocation-size channel, which no
// floor addresses. (Every end-to-end repro in this file binds its secret with
// `let s: i64 @Secret = n` inside a trusted tool; the tests take it as a
// parameter — the same label.)
// ---------------------------------------------------------------------------

/// CLOSED by S8 (was the round-3 open pin): a closure built BEFORE a secret
/// write RETURNS the aggregate element AFTER it. The indirect call's result
/// now carries both of the site's floors. `sigil forge` output 42 / 7 bytes
/// on main and round 3.
#[test]
fn closure_returning_an_aggregate_read_after_a_secret_write_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let f = fn(x: i64) -> i64 { return a[0]; };\n\
         \x20   a[0] = s;\n\
         \x20   return pub_sink(f(0));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an indirect call's result must carry the site's floors"
    );
}

/// CLOSED by S8 (was the round-3 open pin), raw form.
#[test]
fn closure_returning_a_raw_load_after_a_secret_raw_store_is_t001() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let p: i64 = alloc(1);\n\
         \x20   let f = fn(x: i64) -> i64 { return load8(p); };\n\
         \x20   store8(p, s);\n\
         \x20   return pub_sink(f(0));\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an indirect call's result must carry the site's raw-load floor"
    );
}

/// Clean twin: an indirect call at a clean site returns a clean result.
#[test]
fn closure_returning_an_aggregate_read_after_a_public_write_is_clean() {
    let codes = module_code_set(
        "fn probe(k: i64 @Public) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let f = fn(x: i64) -> i64 { return a[0]; };\n\
         \x20   a[0] = k;\n\
         \x20   return pub_sink(f(0));\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a clean site must not floor an indirect call's result; got {codes:?}"
    );
}

/// OPEN (LOAD direction, the SINK-INSIDE form): the closure body SINKS the
/// aggregate read itself and the caller DISCARDS the call's result into a
/// @Secret binding. The body is checked once, at its construct site, with
/// that site's floors — before the write — and S8 floors only what comes OUT
/// of the call (`return f(0)` and a plain `let ignored: i64 = f(0)` from
/// this probe are both rejected). Only S3, or re-checking the body at every
/// invocation site, closes it.
#[test]
fn closure_sinking_an_aggregate_read_inside_itself_after_a_secret_write_is_open() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   let f = fn(x: i64) -> i64 { let leaked: i64 = pub_sink(a[0]); return 0; };\n\
         \x20   a[0] = s;\n\
         \x20   let ignored: i64 @Secret = f(0);\n\
         \x20   return 0;\n}\n",
    );
    if HEAP_FLOOR_PROGRAM_ENTRY {
        assert_eq!(
            codes,
            set(&["T001"]),
            "S3 closes the sink-inside-closure boundary"
        );
    } else {
        assert!(
            codes.is_empty(),
            "pinned OPEN channel (a sink INSIDE a closure body checked before the write); \
             a rule that closes it must flip this pin; got {codes:?}"
        );
    }
}

/// OPEN (allocation size): a @Secret-derived ALLOCATION SIZE moves the bump
/// pointer, and a later `alloc` difference reads it back. No store happens, so
/// no floor rises; only `@SecretCT` sizes are rejected today. `sigil forge`
/// outputs 2 bytes for secret 40 and 3 for 41.
#[test]
fn secret_allocation_size_observed_through_the_bump_pointer_is_open() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public ! { Alloc } {\n\
         \x20   let a0: i64 = alloc(1);\n\
         \x20   let x: i64 @Secret = alloc((s & 1) + 1);\n\
         \x20   let b: i64 = alloc(1);\n\
         \x20   return pub_sink(b - a0);\n}\n",
    );
    assert!(
        codes.is_empty(),
        "pinned OPEN channel (allocation size through the bump pointer); \
         a rule that closes it must flip this pin; got {codes:?}"
    );
}

/// THE REMAINING GAP, pinned with its EXACT code set so it cannot drift
/// silently: an assignment's PLACE is walked for its address label only, into a
/// discarded diagnostic sink, so a sink violation written inside the index —
/// here a @Secret passed to a @Public parameter — never becomes a source
/// diagnostic. What rejects the program instead is the FORMAL bridge, as an
/// I-class toolchain-integrity failure ("formal Lean verifier rejected
/// compiler-produced CSIR"), which names neither the flow nor the line. The
/// pinned main binary at ae026aec produces the identical code set, so this is
/// the pre-existing behavior, not a regression of this rule. Whoever walks the
/// place for diagnostics should expect this to become the T-code instead.
#[test]
fn secret_in_an_assignment_place_index_is_an_integrity_error_not_a_taint_one() {
    let codes = module_code_set(
        "fn probe(s: i64 @Secret) -> i64 @Public {\n\
         \x20   let mut a: [i64; 2] = [0, 0];\n\
         \x20   a[pub_sink(s) & 1] = 1;\n\
         \x20   return 0;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["I013"]),
        "the place's own taint diagnostics are discarded; the formal bridge \
         rejects it as an integrity failure — pinned gap"
    );
}

// ---------------------------------------------------------------------------
// THE RETURNED-POINTER SINK (round 6). The floors label what a READ returns;
// a pointer can reach a sink UNREAD — `tool_main` returns `out << 32 | n` and
// the HOST reads the buffer. The M6 REGION taint is that sink's rule
// (`store8(out, s); return out` was T001 on main), but it was written by ONE
// arm — an expression-statement `store8`, VALUE operand only — so everything
// else that puts a secret behind `out` left the region clean. Each probe below
// was accepted by `sigil check` on main at ae026aec AND leaked end-to-end with
// `sigil forge` (the hex is the forge output for the secret bit 0 / 1). The
// rule is now total: every raw-write intrinsic taints the region of every
// operand with the join of ALL operands and the pc (inline), a callee's
// summary says WHICH parameter slots it can raw-write through so the call
// site taints those arguments' regions at the callee's label bound (S5,
// region side — the review's seventh channel), and a closure body's region
// taint flows back to its construct site. The tool-shaped probes are checked
// through the tool pipeline exactly as `sigil check` runs them, `tool_main`'s
// return being the sink (its effective label is @Internal, so only a @Secret
// region reaches T001 there). Clean twins fence the over-taint; the slot
// precision pin proves the rule keys on the parameter the write went THROUGH.
// ---------------------------------------------------------------------------

/// A whole `module tool;` program, checked as `sigil check` checks a tool.
fn raw_tool_code_set(program: &str) -> BTreeSet<String> {
    compile_tool_codes(program).into_iter().collect()
}

/// The review's g6 probe VERBATIM: the callee MINTS a @Secret and `store8`s it
/// through the caller's pointer; the caller never reads the byte and returns
/// the pointer to the host. `00` / `01` on main.
#[test]
fn callee_storing_its_own_secret_through_a_returned_caller_pointer_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(out, s & 1);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = poke(out);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's secret store through the caller's pointer must taint the \
         returned pointer's region"
    );
}

/// The review's g1 probe: the callee stores a @Public byte, but WHICH byte is
/// chosen under its own @Secret branch — the implicit-flow form of the same
/// channel. `00` / `01` on main. The callee's annotation bound (it mints the
/// secret) is what the call site sees.
#[test]
fn callee_storing_under_its_own_secret_branch_through_a_returned_caller_pointer_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn probe(out: i64) -> i64 @Public ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   if (s & 1) == 1 {\n\
         \x20       store8(out, 1);\n\
         \x20   } else {\n\
         \x20       store8(out, 0);\n\
         \x20   }\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = probe(out);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a callee's store under its own secret branch must taint the returned \
         pointer's region"
    );
}

/// Two calls deep, through an alias and address arithmetic: `poke` rebinds
/// the pointer and hands it on, `inner` writes at `q + 1`. `0001` on main. The
/// slot attribution is transitive over the call graph and over `let`-derived
/// locals.
#[test]
fn callee_storing_its_own_secret_two_calls_deep_through_an_alias_taints_the_returned_pointer_is_t001()
 {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn inner(q: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let r: i64 = q + 1;\n\
         \x20   store8(r, s & 1);\n\
         \x20   return 1;\n}\n\
         fn poke(out: i64) -> i64 @Public {\n\
         \x20   let alias: i64 = out;\n\
         \x20   return inner(alias);\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = poke(out);\n\
         \x20   return out << 32 | 2;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "slot attribution must follow the pointer through a rebind, address \
         arithmetic and a second call"
    );
}

/// CLEAN TWIN 1: the callee stores only a @Public byte through the pointer —
/// the shape of every stdlib writer.
#[test]
fn callee_storing_a_public_byte_through_a_returned_caller_pointer_is_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64) -> i64 @Public {\n\
         \x20   store8(out, 7);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = poke(out);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public-only writer must leave the returned pointer clean; got {codes:?}"
    );
}

/// CLEAN TWIN 2 (the anti-stub): the callee mints and stores its secret into
/// its OWN fresh buffer and never touches the caller's pointer. The floors
/// rise (the secret IS in memory) but the returned pointer's region is
/// untouched — this is what proves the rule keys on the slot a write went
/// THROUGH, not on a secret anywhere in the callee. (The same callee ALSO
/// writing a @Public byte through `out` is the counted false positive pinned
/// below: the label is the annotation bound.)
#[test]
fn callee_storing_its_own_secret_into_its_own_buffer_leaves_the_returned_pointer_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64) -> i64 @Public ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mine: i64 = alloc(8);\n\
         \x20   store8(mine, s & 1);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = poke(out);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a secret stored into the callee's OWN buffer must not taint the caller's \
         pointer; got {codes:?}"
    );
}

/// CLEAN TWIN 3: the callee writes its secret through the caller's pointer, but
/// the caller never returns (or reads through) that pointer. The region is
/// tainted; nothing observes it.
#[test]
fn callee_storing_its_own_secret_through_a_caller_pointer_that_is_never_returned_is_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(out, s & 1);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = poke(out);\n\
         \x20   return n;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a tainted region nobody returns or reads must not reject; got {codes:?}"
    );
}

/// SLOT PRECISION: the callee writes its secret through its SECOND parameter
/// and never touches the first; the caller hands the returned buffer as the
/// FIRST. Only slot 1's argument (a scratch buffer nobody returns) is tainted —
/// the summary names the slot, it does not say `All`.
#[test]
fn callee_storing_through_a_different_parameter_leaves_the_returned_pointer_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64, scratch: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(scratch, s & 1);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let scratch: i64 = alloc(8);\n\
         \x20   let n: i64 = poke(out, scratch);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "the region taint must land on the argument filling the WRITTEN slot only; \
         got {codes:?}"
    );
}

/// The same slot-precision program with the arguments SWAPPED — the returned
/// buffer now fills the written slot — is the leak, so the clean pin above is
/// not clean by accident.
#[test]
fn callee_storing_through_the_parameter_the_returned_pointer_fills_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64, scratch: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(scratch, s & 1);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let scratch: i64 = alloc(8);\n\
         \x20   let n: i64 = poke(scratch, out);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the returned buffer fills the written slot, so its region is tainted"
    );
}

/// COUNTED FALSE POSITIVE (the region side of the S5 annotation bound): a
/// callee that MENTIONS a @Secret it never stores, and writes a @Public byte
/// through the caller's pointer, taints that region — `annotation` is a
/// syntactic upper bound on what the callee could have written, the same cost
/// `callee_that_mentions_a_secret_but_writes_public_is_a_counted_false_positive`
/// pins for the floors. Recorded, not hidden.
#[test]
fn callee_mentioning_a_secret_but_storing_public_through_the_returned_pointer_is_a_counted_false_positive()
 {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn poke(out: i64) -> i64 @Public {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(out, 7);\n\
         \x20   return 1;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let n: i64 = poke(out);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "counted cost: the annotation bound, not the stored value, labels the write"
    );
}

/// An UNNAMED callee (a closure invoked through a local) takes the program-wide
/// bound — `All` slots — so the pointer handed to it is tainted at the bound.
/// Here the closure writes through its own PARAMETER, which no capture rule
/// sees. The call's RESULT is bound at @Secret and discarded: the S9 floor that
/// flows back from the body already labels it, so returning it — or binding it
/// at @Public — would be T001 for another reason (mutation A left the first two
/// drafts green). Only the region path reaches this return. Fail closed.
#[test]
fn indirect_callee_storing_its_own_secret_through_a_handed_pointer_taints_it_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let c = fn(p: i64) -> i64 { let s: i64 @Secret = 1; store8(p, s & 1); return 1; };\n\
         \x20   let ignored: i64 @Secret = c(out);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an unnamed callee may write through every pointer it is handed"
    );
}

/// INLINE, the ADDRESS channel through the sink: `store8(out + (s & 1), 9)`
/// writes a @Public byte, but the host sees WHICH cell changed — `0900` /
/// `0009` on main, where the `Store8` arm read the value operand only.
#[test]
fn secret_address_store_taints_the_returned_pointer_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(out + (s & 1), 9);\n\
         \x20   return out << 32 | 2;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the region takes the join of every store operand, the address included"
    );
}

/// INLINE, `vec_store` is a raw write like `store8`: `00` / `01` on main, where
/// the region arm matched `Store8` alone.
#[test]
fn vec_store_of_a_secret_taints_the_returned_pointer_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   vec_store(out, 0, 64, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "every raw-write intrinsic taints the region it writes through"
    );
}

/// CLEAN TWIN for the two inline pins: @Public bytes at @Public addresses,
/// both intrinsics, then the pointer is returned.
#[test]
fn public_stores_at_public_addresses_leave_the_returned_pointer_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let i: i64 = 1;\n\
         \x20   store8(out + i, 9);\n\
         \x20   vec_store(out, 2, 64, 5);\n\
         \x20   return out << 32 | 3;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "public writes must not taint the region; got {codes:?}"
    );
}

/// A CLOSURE that mints its own secret and stores it through a CAPTURED
/// pointer: the closure value carries only its captures' labels (`out` is
/// @Public), and the body was checked in an env with no regions, so `00` /
/// `01` on main. The captured pointer keeps its region inside the body and the
/// body's region taint flows back to the construct site. The call's result is
/// bound at @Secret and discarded — the S9 floor flowed back from the body
/// labels it, and a @Public `let` of it would be T001 for that other reason
/// (mutation B left the first draft green) — so only the region path reaches
/// the return.
#[test]
fn closure_minting_its_own_secret_and_storing_through_a_captured_pointer_taints_it_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let c = fn(x: i64) -> i64 { let s: i64 @Secret = 1; store8(out, s & 1); return x; };\n\
         \x20   let ignored: i64 @Secret = c(1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a closure body's store through a captured pointer must taint the \
         enclosing region"
    );
}

/// CLEAN TWIN: the closure stores a @Public byte through the captured pointer.
#[test]
fn closure_storing_a_public_byte_through_a_captured_pointer_leaves_it_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let c = fn(x: i64) -> i64 { store8(out, 7); return x; };\n\
         \x20   let n: i64 = c(1);\n\
         \x20   return out << 32 | n;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store in a closure must not taint the captured region; got {codes:?}"
    );
}

/// OPEN (the unregioned-pointer surface, array-element shape), pinned as an
/// exact ACCEPT so it cannot drift silently: the M6 model regions only locals
/// bound to `alloc`, or to `+`/`-` arithmetic over `alloc` calls and regioned
/// locals, so a pointer read out of an aggregate — here
/// `a[0]` — has no region, the store through it taints nothing and the
/// returned `out` hands the host the byte. `00` / `01` on main and here. The
/// same surface covers a parameter (the next pin), a callee's result, other
/// arithmetic, a pointer reloaded from memory, a record field (the pin after)
/// and a state field. Closing it needs a rule total over every pointer-valued
/// expression kind — a design, not a landing-pass edit. Disclosed in
/// `CLAIMS.md` §C HF-1 and `SOUNDNESS_MATRIX.md` SND-IFC-001; a rule that
/// closes it must flip this pin.
#[test]
fn pointer_smuggled_through_an_array_element_then_stored_through_is_open() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let a: [i64; 1] = [out];\n\
         \x20   store8(a[0], s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "pinned OPEN channel (a pointer smuggled through memory has no region); \
         a rule that closes it must flip this pin; got {codes:?}"
    );
}

/// OPEN (the same unregioned-pointer surface, its most natural shape), pinned
/// as an exact ACCEPT: the caller's PARAMETER pointer. `tool_main`'s own
/// `input_ptr` is the host's buffer; a parameter is not an `alloc` result, so
/// it has no region, the store through it is attributed to nothing, and the
/// returned pointer hands the host the bit. `00` / `01` end-to-end on main and
/// on this branch (the round-6 review's p1, verbatim; via a callee `poke(
/// input_ptr)` too — p2). The corpus already has an input-echo tool that
/// returns `input_ptr` packed the same way, so this is the shape an agent
/// writes first. A rule that regions parameters must flip this pin.
#[test]
fn secret_stored_through_the_parameter_pointer_then_returned_is_open() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(input_ptr, s & 1);\n\
         \x20   return input_ptr << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "pinned OPEN channel (a parameter pointer has no region); \
         a rule that closes it must flip this pin; got {codes:?}"
    );
}

/// OPEN (the same surface, through a record field), pinned as an exact
/// ACCEPT: `b.p` is a field read, not a regioned local, so the store through it
/// is attributed to nothing and the returned `out` carries the bit. `00` /
/// `01` end-to-end on main and on this branch (the round-6 review's q1,
/// verbatim). Returning `b.p` ITSELF is T001 through the S4 typed-read floor;
/// only the unread `out` leaks.
#[test]
fn secret_stored_through_a_record_field_pointer_then_returned_is_open() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         record Buf { p: i64 }\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let b: Buf = Buf { p: out };\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(b.p, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "pinned OPEN channel (a pointer read out of a record field has no region); \
         a rule that closes it must flip this pin; got {codes:?}"
    );
}

// ---------------------------------------------------------------------------
// THE RETURNED-POINTER SINK ACROSS CONTROL FLOW (round 7). The M6 region facts
// — which region a pointer local points into, and what was stored into each
// region — were joined at NO control-flow merge: `loop_fixpoint` rebuilt each
// pass's env without them and the real pass walked the body ONCE with every
// pointer in its pre-loop region; `if`/`match` arms wrote one shared map and
// the last writer won; a block's shadow left ITS region on the outer name.
// Each shape below was `check` clean and printed the bit with `sigil forge`
// on main (`00` / `01`, probes r1..r14 of the round-7 pass); the same rebind
// inside a callee was already closed by the flow-insensitive S5 scan. The
// region map is now a per-path fact joined like the bindings (union of the
// candidate regions — a store through the local taints every candidate), the
// region taint is loop-carried, and the shadow restores the outer region.
// Every leak is pinned exact `T001`; the twins pin what the join must NOT
// over-taint.
// ---------------------------------------------------------------------------

/// The round-6 review's q5 VERBATIM: `q` is rebound to `out` inside the loop,
/// so the second iteration's store lands in the returned buffer. `00` / `01`
/// on main.
#[test]
fn pointer_rebound_across_a_loop_back_edge_taints_the_returned_region_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       store8(q, s & 1);\n\
         \x20       q = out;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the loop-carried region map must attribute iteration two's store to `out`"
    );
}

/// CLEAN TWIN: the same loop stores a @Public byte only. The join must not
/// invent taint — `07` on main, and accepted here.
#[test]
fn pointer_rebound_across_a_loop_back_edge_storing_only_public_stays_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       store8(q, 7);\n\
         \x20       q = out;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store through the rebound pointer must not taint `out`; got {codes:?}"
    );
}

/// CLEAN TWIN: `q` is rebound to a FRESH buffer every iteration and the secret
/// goes into those; `out` is never written. `00` / `00` on main, accepted here
/// — the join must not merge `out` into `q`'s candidates.
#[test]
fn pointer_rebound_to_a_fresh_alloc_each_iteration_leaves_the_returned_buffer_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       store8(q, s & 1);\n\
         \x20       q = alloc(8);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "secret stores into fresh per-iteration buffers must not taint `out`; got {codes:?}"
    );
}

/// The store sits in an INNER loop and the rebind in the outer: the inner
/// fixpoint runs inside every outer pass, so the outer head's region map must
/// reach it. `00` / `01` on main.
#[test]
fn pointer_rebound_across_a_nested_loop_back_edge_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       let mut j: i64 = 0;\n\
         \x20       while j < 2 {\n\
         \x20           store8(q, s & 1);\n\
         \x20           j = j + 1;\n\
         \x20       }\n\
         \x20       q = out;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the outer head's region map must reach the inner loop's store"
    );
}

/// Two rebinds: `out` reaches `q` only on the THIRD iteration (`q = r; r =
/// out`), so a single extra pass is not enough — the fixpoint must run to
/// convergence. `00` / `01` on main.
#[test]
fn pointer_rebound_twice_across_loop_back_edges_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let mut r: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 3 {\n\
         \x20       store8(q, s & 1);\n\
         \x20       q = r;\n\
         \x20       r = out;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a two-step rebind chain must converge to `out` in `q`'s candidates"
    );
}

/// The `for` RANGE form of the loop. `00` / `01` on main.
#[test]
fn pointer_rebound_across_a_for_range_back_edge_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   for i in 0..2 {\n\
         \x20       store8(q, s & 1);\n\
         \x20       q = out;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "`for` range loops carry the region map too"
    );
}

/// The `for`-IN form of the loop. `00` / `01` on main.
#[test]
fn pointer_rebound_across_a_for_in_back_edge_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let xs: [i64; 2] = [0, 0];\n\
         \x20   for x in xs {\n\
         \x20       store8(q, s & 1);\n\
         \x20       q = out;\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "`for`-in loops carry the region map too"
    );
}

/// The rebind reaches the head only through a `continue` (the fall-through
/// path rebinds to a fresh buffer), so the continue snapshots must carry the
/// region map. `00` / `01` on main.
#[test]
fn pointer_rebound_on_a_continue_path_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 3 {\n\
         \x20       i = i + 1;\n\
         \x20       store8(q, s & 1);\n\
         \x20       if i == 1 {\n\
         \x20           q = out;\n\
         \x20           continue;\n\
         \x20       }\n\
         \x20       q = alloc(8);\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a `continue` path's region map must be joined into the loop head"
    );
}

/// An `if` JOIN, no loop: one branch rebinds `q` to `out`, the other to a
/// fresh buffer, and the store after the join must be attributed to BOTH.
/// Before, the last-walked branch's map won (`00` / `01` on main; swapping
/// the branches made main reject it — order-dependent).
#[test]
fn pointer_rebound_in_one_if_branch_is_attributed_at_the_join_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   if input_len > 0 {\n\
         \x20       q = out;\n\
         \x20   } else {\n\
         \x20       q = alloc(8);\n\
         \x20   }\n\
         \x20   store8(q, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the `if` join must keep `out` among `q`'s candidate regions"
    );
}

/// CLEAN TWIN of the `if` join: both branches rebind to fresh buffers, so
/// `out` is in NO path's candidates and the join must not resurrect it from
/// the pre-branch map. `00` / `00` on main, accepted here.
#[test]
fn pointer_rebound_to_fresh_allocs_in_both_if_branches_leaves_the_returned_buffer_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   if input_len > 0 {\n\
         \x20       q = alloc(8);\n\
         \x20   } else {\n\
         \x20       q = alloc(8);\n\
         \x20   }\n\
         \x20   store8(q, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "an `if` whose branches both rebind away from `out` must not taint it; got {codes:?}"
    );
}

/// A `match` JOIN: the FIRST arm rebinds to `out`, the last to a fresh
/// buffer. `00` / `01` on main (the mirror image, `out` in the last arm, was
/// rejected there — the last arm's map won).
#[test]
fn pointer_rebound_in_a_match_arm_is_attributed_at_the_join_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = alloc(8);\n\
         \x20   let o: Option<i64> = Some(1);\n\
         \x20   match o {\n\
         \x20       Some(v) => { q = out; },\n\
         \x20       None => { q = alloc(8); },\n\
         \x20   }\n\
         \x20   store8(q, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the `match` join must keep `out` among `q`'s candidate regions"
    );
}

/// A SHADOW: the secret is stored through the OUTER `out` before the block;
/// the inner `let out` used to leave its clean region on the outer name at
/// the block's end, so the return read the inner region. `00` / `01` on main.
/// Closed by the `if` JOIN (the then-arm's map still names the inner region
/// when the restore is disabled, and the union with the else-arm keeps the
/// outer one — mutation D left this pin green); the shadow RESTORE is what
/// keeps the twin below clean.
#[test]
fn shadowed_pointer_keeps_its_outer_region_after_the_block_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   store8(out, s & 1);\n\
         \x20   if input_len > 0 {\n\
         \x20       let out: i64 = alloc(8);\n\
         \x20       store8(out, 7);\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "the block's end must restore the OUTER region on the shadowed name"
    );
}

/// CLEAN TWIN of the shadow: the secret goes into the INNER buffer only and
/// the outer `out` is returned. Main REJECTED this (the inner, tainted region
/// stayed on the outer name — a false positive the restore removes); accepted
/// here, since the outer buffer never held the secret. This is the pin the
/// shadow restore is load-bearing for (mutation D: exactly this one red).
#[test]
fn shadow_storing_a_secret_into_its_own_buffer_leaves_the_outer_buffer_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   if input_len > 0 {\n\
         \x20       let out: i64 = alloc(8);\n\
         \x20       store8(out, s & 1);\n\
         \x20   }\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a secret stored into a shadow's own buffer must not taint the outer one; got {codes:?}"
    );
}

/// COUNTED FALSE POSITIVE (the one precision cost of the loop-carried region
/// facts): the fixpoint mints a body `alloc`'s region at the SAME id on every
/// pass, so all iterations' buffers from one site share a region — the join
/// over iterations, which is what keeps the state finite. A pointer allocated
/// in the body and sunk BEFORE this iteration's store therefore reads the
/// taint an EARLIER iteration stored through the same site's (different)
/// buffer. Accepted on main (`check` clean, the round-7 probe c1); rejected
/// here. Zero corpus instances; the alternative — a fresh region per
/// iteration — is an unbounded state, not a fixpoint. Disclosed in
/// `CLAIMS.md` §C HF-1.
#[test]
fn pointer_allocated_inside_a_loop_body_sunk_before_the_iterations_store_is_a_counted_false_positive()
 {
    let codes = raw_tool_code_set(
        "module tool;\n\
         fn pub_sink(x: i64 @Public) -> i64 @Public {\n    return x;\n}\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   let mut n: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       let p: i64 = alloc(8);\n\
         \x20       n = pub_sink(p);\n\
         \x20       store8(p, s & 1);\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   return n;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "counted cost: same-site body allocations share one region across iterations"
    );
}

// ---------------------------------------------------------------------------
// AN `alloc` INSIDE THE BOUND VALUE'S `+`/`-` CHAIN (round 8). Until round 8 a
// `let`/rebind minted a region only when the value WAS the `alloc` call
// (`is_alloc_expr`), and `region_of_expr` — `&self`, it cannot mint — gave a
// bare `alloc(..)` operand no region, so `let q = alloc(8) + 0` bound an
// UNREGIONED local: the store through `q` taints nothing and `return q << 32
// | 1` hands the host the bit. `check` clean and `00` / `01` on main and on
// round 7 — while every disclosure site said the model regions "locals
// derived from `alloc` by `+`/`-`". `regions_of_bound_value` now walks the
// chain at both binding sites: every `alloc` leaf mints, every local leaf
// contributes its regions, a mixed chain is attributed to both. Every leak is
// pinned exact `T001`; the twins pin what the mint must NOT over-taint (a
// public store; a buffer never returned).
// ---------------------------------------------------------------------------

/// The round-7 review's blocker VERBATIM: `alloc(8) + 0` bound directly.
#[test]
fn alloc_plus_zero_bound_directly_then_stored_through_and_returned_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let q: i64 = alloc(8) + 0;\n\
         \x20   store8(q, s & 1);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an `alloc` inside the bound value's `+` chain must mint `q`'s region"
    );
}

/// CLEAN TWIN: the same binding stores a @Public byte only. The mint must not
/// invent taint.
#[test]
fn alloc_plus_zero_bound_directly_storing_only_public_stays_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let q: i64 = alloc(8) + 0;\n\
         \x20   store8(q, 7);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store through a chain-minted region must not taint it; got {codes:?}"
    );
}

/// `-` is the other half of the chain rule.
#[test]
fn alloc_minus_zero_bound_directly_then_stored_through_and_returned_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let q: i64 = alloc(8) - 0;\n\
         \x20   store8(q, s & 1);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an `alloc` inside the bound value's `-` chain must mint `q`'s region"
    );
}

/// The offset is a @Public LOCAL, not a literal: the local leaf contributes no
/// region (`k` is a scalar) and the `alloc` leaf still mints.
#[test]
fn alloc_plus_a_public_offset_local_bound_directly_then_stored_through_and_returned_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let k: i64 = 4;\n\
         \x20   let q: i64 = alloc(8) + k;\n\
         \x20   store8(q, s & 1);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an `alloc` plus a public local must mint `q`'s region"
    );
}

/// CLEAN TWIN: the chain-minted buffer is written but NEVER returned; the
/// returned `out` was allocated before the store (so the S2 floor's `alloc`
/// counted cost does not apply) and never held the secret.
#[test]
fn alloc_plus_a_public_offset_local_stored_through_but_never_returned_stays_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let k: i64 = 4;\n\
         \x20   let q: i64 = alloc(8) + k;\n\
         \x20   store8(q, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a secret stored into a chain-minted buffer must not taint an unrelated one; got {codes:?}"
    );
}

/// The `alloc` is two `+` deep: the walk is recursive over the whole chain,
/// not a one-level peek.
#[test]
fn alloc_nested_two_deep_in_the_chain_bound_directly_then_stored_through_and_returned_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let q: i64 = (alloc(8) + 4) + 4;\n\
         \x20   store8(q, s & 1);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "an `alloc` two `+` deep in the bound value must still mint `q`'s region"
    );
}

/// A REBIND inside a loop: `q = alloc(8) + 8` each iteration, the secret
/// stored through the loop-carried `q` AFTER the loop, `q` returned. Until
/// round 8 the rebind CLEARED `q`'s region (the value is not the `alloc`
/// call), so the store tainted nothing and the program was accepted — `00` /
/// `01` on main and on round 7. Here the rebind mints at the loop's stable id,
/// the exit join carries that region on `q`, and the store lands in it. (The
/// store INSIDE the loop is a different pin: the first iteration's secret
/// store raises the S2 floor and the next iteration's `alloc` — an intrinsic
/// result, a typed read — is floored, so round 7 already rejected that shape
/// through the floors; it does not exercise the mint.)
#[test]
fn pointer_rebound_to_an_alloc_chain_across_a_loop_back_edge_then_returned_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       q = alloc(8) + 8;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   store8(q, s & 1);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a loop rebind to an `alloc` chain must mint the region the store then taints"
    );
}

/// CLEAN TWIN of the loop rebind: a @Public byte only (`07` on every binary).
#[test]
fn pointer_rebound_to_an_alloc_chain_across_a_loop_back_edge_storing_only_public_stays_clean() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let mut q: i64 = 0;\n\
         \x20   let mut i: i64 = 0;\n\
         \x20   while i < 2 {\n\
         \x20       q = alloc(8) + 8;\n\
         \x20       i = i + 1;\n\
         \x20   }\n\
         \x20   store8(q, 7);\n\
         \x20   return q << 32 | 1;\n}\n",
    );
    assert!(
        codes.is_empty(),
        "a public store through a loop-rebound chain region must not taint it; got {codes:?}"
    );
}

/// FAIL CLOSED on a MIXED chain: `alloc(8) + out` names an `alloc` leaf AND a
/// regioned local, so `q` is attributed to BOTH regions and the store through
/// it taints `out` too — the returned `out` is rejected. This pins the UNION,
/// not a closure: the local leaf already contributed `out`'s region before
/// round 8 (`T001` on main and on round 7 too), and the mint must not REPLACE
/// it with the fresh region. (At runtime such a sum is not a pointer into
/// either buffer; the rule over-approximates rather than pick one operand.)
#[test]
fn alloc_plus_a_regioned_local_bound_directly_taints_both_regions_is_t001() {
    let codes = raw_tool_code_set(
        "module tool;\n\
         pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc } {\n\
         \x20   let out: i64 = alloc(64);\n\
         \x20   let s: i64 @Secret = 1;\n\
         \x20   let q: i64 = alloc(8) + out;\n\
         \x20   store8(q, s & 1);\n\
         \x20   return out << 32 | 1;\n}\n",
    );
    assert_eq!(
        codes,
        set(&["T001"]),
        "a chain mixing an `alloc` with a regioned local must be attributed to both regions"
    );
}
