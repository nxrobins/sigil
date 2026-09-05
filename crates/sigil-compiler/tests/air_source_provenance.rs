//! Instruction sites survive lowering even when an instruction has no result.
//! This is projection provenance, not an occurrence-safety verdict.

use sigil_compiler::air::{self, AirProgram, AirStmt, AirTerminator};
use sigil_compiler::compile_named_module;
use sigil_test_utils::pipeline::typecheck_or_panic;

fn statement_sites<'a>(
    source: &'a str,
    program: &AirProgram,
    select: impl Fn(&AirStmt) -> bool,
) -> Vec<(usize, &'a str)> {
    let mut sites = Vec::new();
    for function in &program.functions {
        for block in &function.blocks {
            for (index, statement) in block.stmts.iter().enumerate() {
                if select(statement) {
                    let index = u32::try_from(index).expect("fixture statement index fits");
                    let span = function
                        .security
                        .statement_spans
                        .get(&(block.id, index))
                        .expect("a source instruction must retain its own span");
                    assert_ne!(*span, function.def_span, "not a whole-function fallback");
                    sites.push((span.start, &source[span.start..span.end]));
                }
            }
        }
    }
    sites.sort_by_key(|(offset, _)| *offset);
    sites
}

#[test]
fn repeated_send_sites_and_nested_argument_spans_are_distinct() {
    let source = r#"module sites;
actor Worker { init() {} on Ping(value: i64) {} }
fn value() -> i64 { return 7; }
fn run(worker: ActorRef<Worker>, flag: bool) {
    worker.send(Ping(value()));
    if flag { worker.send(Ping(8)); } else { worker.send(Ping(9)); }
    worker.send(Ping(value()));
}
"#;
    let raw = air::lower(&typecheck_or_panic(source));
    let sends = statement_sites(source, &raw, |statement| {
        matches!(statement, AirStmt::MessageSend { .. })
    });
    assert_eq!(
        sends.iter().map(|(_, text)| *text).collect::<Vec<_>>(),
        [
            "worker.send(Ping(value()))",
            "worker.send(Ping(8))",
            "worker.send(Ping(9))",
            "worker.send(Ping(value()))",
        ]
    );
    assert_ne!(
        sends[0].0, sends[3].0,
        "identical syntax has different sites"
    );
    assert_eq!(
        statement_sites(source, &raw, |statement| {
            matches!(statement, AirStmt::SerializeMessage { .. })
        }),
        sends,
        "serialization belongs to the enclosing send, not its last argument"
    );
    assert_eq!(
        statement_sites(source, &raw, |statement| matches!(
            statement,
            AirStmt::Call { .. }
        ))
        .iter()
        .map(|(_, text)| *text)
        .collect::<Vec<_>>(),
        ["value()", "value()"]
    );
}

#[test]
fn zero_argument_external_calls_keep_exact_sites() {
    let source = r#"#[ring(outer)] #[trusted] module sites;
extern "C" fn tick() -> i64 ! { FFI, Unsafe };
extern "C" fn consume(value: i64) -> i64 ! { FFI, Unsafe };
fn value() -> i64 { return 7; }
fn run() ! { FFI, Unsafe } {
    tick();
    consume(value());
    tick();
}
"#;
    let raw = air::lower(&typecheck_or_panic(source));
    assert_eq!(
        statement_sites(source, &raw, |statement| {
            matches!(statement, AirStmt::ExternCall { .. })
        })
        .iter()
        .map(|(_, text)| *text)
        .collect::<Vec<_>>(),
        ["tick()", "consume(value())", "tick()"]
    );
}

#[test]
fn loop_header_calls_and_state_writes_keep_their_source_sites() {
    let source = r#"module sites;
actor Counter {
    state { mut n: i64 }
    init() { n = 0; }
    on Set(value: i64) { n = value; }
}
fn guard(flag: bool) -> bool { return flag; }
fn run(flag: bool) -> i64 {
    let mut again = flag;
    while guard(again) { again = false; }
    return 0;
}
"#;
    let raw = air::lower(&typecheck_or_panic(source));
    assert_eq!(
        statement_sites(source, &raw, |statement| {
            matches!(statement, AirStmt::StateWrite { .. })
        })
        .iter()
        .map(|(_, text)| *text)
        .collect::<Vec<_>>(),
        ["n = 0;", "n = value;"]
    );
    let mut loop_sites = Vec::new();
    for function in &raw.functions {
        for block in &function.blocks {
            if matches!(block.terminator, AirTerminator::Loop { .. }) {
                let span = function.security.terminator_spans[&block.id];
                loop_sites.push(&source[span.start..span.end]);
            }
        }
    }
    assert_eq!(loop_sites, ["guard(again)"]);
    assert_eq!(
        statement_sites(source, &raw, |statement| matches!(
            statement,
            AirStmt::Call { .. }
        ))
        .iter()
        .map(|(_, text)| *text)
        .collect::<Vec<_>>(),
        ["guard(again)"]
    );
}

#[test]
fn span_only_changes_do_not_change_csir_wasm_or_air_snapshots() {
    let source =
        "module sites; fn run(flag: bool) -> i64 { if flag { return 1; } else { return 2; } }";
    let shifted = format!("// source locations are outside certificate bytes\n\n{source}");
    let first = compile_named_module("sites.sigil", source).expect("baseline compiles");
    let second = compile_named_module("sites.sigil", shifted).expect("shifted source compiles");
    let first_raw = air::lower(&first.typed);
    let second_raw = air::lower(&second.typed);
    let branch_sites = first_raw
        .functions
        .iter()
        .flat_map(|function| {
            function.blocks.iter().filter_map(|block| {
                if matches!(block.terminator, AirTerminator::Branch { .. }) {
                    let span = function.security.terminator_spans[&block.id];
                    Some(&source[span.start..span.end])
                } else {
                    None
                }
            })
        })
        .collect::<Vec<_>>();
    assert_eq!(branch_sites, ["flag"]);
    assert_ne!(
        first_raw.functions[0].security.statement_spans,
        second_raw.functions[0].security.statement_spans
    );
    assert_ne!(
        first_raw.functions[0].security.terminator_spans,
        second_raw.functions[0].security.terminator_spans
    );
    assert_eq!(format!("{first_raw:?}"), format!("{second_raw:?}"));
    assert_eq!(first.wasm_inner, second.wasm_inner);
    assert_eq!(first.wasm_outer, second.wasm_outer);
    assert_eq!(first.formal_security_report, second.formal_security_report);
}
