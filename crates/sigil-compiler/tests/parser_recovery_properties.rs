//! Property fence for the unbounded-untrusted-input class (recovery half).
//!
//! `parser_depth_properties.rs` fences one way a parser can fail to return:
//! recursive descent without a depth bound. This file fences the other:
//! error recovery that does not consume anything.
//!
//! `synchronize_item` deliberately breaks WITHOUT consuming when it reaches a
//! `}`, an item start, or a module start, so the caller can parse that token
//! itself. Every caller that loops on `!is_eof() && !at_rbrace()` must check
//! that recovery actually moved. One did not, and because `at_item_start()`
//! includes `at_fn()`, a `fn` item inside an `actor` body parked the cursor
//! forever — `check` never returned on a ~150-byte program, pushing a
//! heap-allocated `Diagnostic` every iteration, so it was unbounded memory
//! growth as well as a hang. Reproduced 2026-08-04 (nested `actor`) and
//! 2026-08-06 (`fn` in `actor`); live since 2026-05-06; SR-016.
//!
//! The property, over every item-start keyword in every block context that
//! recovers: parsing TERMINATES. Termination cannot be proven by the test
//! merely finishing — unlike a stack overflow, a spin does not abort the
//! process — so each parse runs on its own thread behind a deadline, and the
//! deadline itself is proven to fire (SC-P4) by a planted spin below.

use std::sync::mpsc;
use std::time::Duration;

use sigil_compiler::compile_named_module;

/// A parse of one of these fixtures is sub-millisecond; the pre-fix behaviour
/// was unbounded. Anything in between is already a defect worth failing on.
const DEADLINE: Duration = Duration::from_secs(20);

/// Run `work` behind a deadline. `None` means it did not finish in time.
///
/// A timed-out worker cannot be killed, so it is deliberately leaked: the test
/// process is already failing at that point, and a leaked spinning thread is a
/// louder signal than a silent pass.
fn run_within<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> Option<T> {
    let (tx, rx) = mpsc::channel();
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let _ = tx.send(work());
        })
        .expect("spawn parse thread");
    rx.recv_timeout(DEADLINE).ok()
}

fn parse_terminates(source: String) -> bool {
    run_within(move || {
        let _ = compile_named_module("recovery_prop".to_string(), source);
    })
    .is_some()
}

/// Every token `at_item_start()` / `at_module_start()` recognises. Recovery
/// stops on each of these without consuming, so each is a candidate spin.
const ITEM_STARTS: &[&str] = &[
    "fn f() -> i64 { return 1; }",
    "actor Inner { on Tick() -> i64 { return 1; } }",
    "entry actor Inner { on Tick() -> i64 { return 1; } }",
    "use other;",
    "const K: i64 = 1;",
    "cap type Extra {}",
    "type Alias = i64;",
    "record R { a: i64 }",
    "module inner;",
];

/// A named block context and the wrapper that embeds an item inside it.
type Context = (&'static str, fn(&str) -> String);

/// Block contexts whose loops recover with `synchronize_item`.
fn contexts() -> Vec<Context> {
    vec![
        ("actor body", |item| {
            format!("module sigil;\ncap type Fuel {{}}\nentry actor Main {{\n{item}\n}}\n")
        }),
        ("state block", |item| {
            format!(
                "module sigil;\ncap type Fuel {{}}\nentry actor Main {{\n  state {{\n{item}\n  }}\n  on Tick() -> i64 {{ return 1; }}\n}}\n"
            )
        }),
        ("record body", |item| {
            format!("module sigil;\nrecord R {{\n{item}\n}}\n")
        }),
        ("braced module body", |item| {
            format!("module sigil {{\n{item}\n}}\n")
        }),
        ("top level", |item| format!("module sigil;\n{item}\n")),
    ]
}

#[test]
fn item_starts_in_every_recovering_block_terminate() {
    let mut checked = 0usize;
    for (context, wrap) in contexts() {
        for item in ITEM_STARTS {
            let source = wrap(item);
            assert!(
                parse_terminates(source),
                "parse did NOT terminate within {DEADLINE:?}: `{item}` in {context}. \
                 Recovery parked on a token it will never consume — the SR-016 class. \
                 Every loop that calls `synchronize_item` must check \
                 `synchronize_item_made_progress`."
            );
            checked += 1;
        }
    }
    // Anti-vacuity: a wrapper table that silently emptied would pass above.
    assert_eq!(
        checked,
        ITEM_STARTS.len() * 5,
        "the context/item matrix shrank — this fence covers less than it claims"
    );
}

/// The two archived reproductions, verbatim in shape.
#[test]
fn the_archived_reproductions_terminate() {
    let fn_in_actor = "module tool;\ncap type WorkAuth {}\nactor Trio {\n    fn on_inc(n: i64) -> i64 {\n        return n + 1;\n    }\n}\n";
    let nested_actor = "module tool;\ncap type WorkAuth {}\nactor Calc {\n    actor Init {\n        fn init(auth: WorkAuth) {}\n    }\n}\n";
    assert!(
        parse_terminates(fn_in_actor.to_string()),
        "the 2026-08-06 `fn`-in-actor reproduction hangs again"
    );
    assert!(
        parse_terminates(nested_actor.to_string()),
        "the 2026-08-04 nested-actor reproduction hangs again"
    );
}

/// SC-P4: an absence claim needs a proven detector. Every assertion above reads
/// "did not time out", which is worthless if the deadline cannot fire. Plant a
/// spin and show it does.
#[test]
fn the_deadline_detector_actually_fires() {
    let (tx, rx) = mpsc::channel::<()>();
    std::thread::spawn(move || {
        // Never sends. Leaked deliberately; the process outlives it.
        std::thread::sleep(Duration::from_secs(3600));
        let _ = tx.send(());
    });
    assert!(
        rx.recv_timeout(Duration::from_millis(200)).is_err(),
        "the deadline did not fire on a planted non-terminating worker — \
         every termination assertion in this file would pass vacuously"
    );

    // And the positive half: work that DOES finish is reported as finished.
    assert_eq!(
        run_within(|| 7usize),
        Some(7),
        "run_within reported a terminating worker as timed out"
    );
}
