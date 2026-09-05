use sigil_compiler::{
    air::{AirStmt, AirTerminator, AirValue},
    ast::BinaryOp,
    compile_named_module,
    lexer::{TokenKind, lex},
    source::SourceFile,
};

fn codes(source: &str) -> Vec<String> {
    match compile_named_module("ergonomics.sigil", source) {
        Ok(_) => Vec::new(),
        Err(error) => error
            .diagnostics()
            .iter()
            .map(|diagnostic| diagnostic.code().as_str().to_owned())
            .collect(),
    }
}

#[test]
fn logical_tokens_use_maximal_munch() {
    let source = SourceFile::new("tokens.sigil", "a && b & c &= d || e | f |= g");
    let (tokens, diagnostics) = lex(&source);
    assert!(diagnostics.is_empty());
    let kinds: Vec<_> = tokens.into_iter().map(|token| token.kind).collect();
    assert!(matches!(kinds[1], TokenKind::AndAnd));
    assert!(matches!(kinds[3], TokenKind::Ampersand));
    assert!(matches!(kinds[5], TokenKind::AmpersandEq));
    assert!(matches!(kinds[7], TokenKind::OrOr));
    assert!(matches!(kinds[9], TokenKind::Pipe));
    assert!(matches!(kinds[11], TokenKind::PipeEq));
}

#[test]
fn logical_operators_are_bool_only() {
    let source = "module main; fn bad() -> bool { return 1 && 2; }";
    assert!(codes(source).iter().any(|code| code == "T054"));
}

#[test]
fn logical_expressions_normalize_to_control_flow_before_air() {
    let source = r#"
module main;
fn rhs(v: bool) -> bool { return v; }
fn probe(a: bool, b: bool, c: bool) -> bool {
    let x: bool = a || b && rhs(c);
    return x;
}
"#;
    let compilation = compile_named_module("logical_air.sigil", source)
        .expect("logical expression should compile");
    let probe = compilation
        .air
        .functions
        .iter()
        .find(|function| function.name.ends_with("probe"))
        .expect("probe AIR");
    assert!(
        probe
            .blocks
            .iter()
            .filter(|block| matches!(block.terminator, AirTerminator::Branch { .. }))
            .count()
            >= 2,
        "both logical operators must become branches"
    );
    for block in &probe.blocks {
        for statement in &block.stmts {
            if let AirStmt::Assign {
                val: AirValue::Binary { op, .. },
                ..
            } = statement
            {
                assert!(
                    !matches!(op, BinaryOp::LogicalAnd | BinaryOp::LogicalOr),
                    "logical operators must not reach eager AIR binary lowering"
                );
            }
        }
    }
    wasmparser::Validator::new()
        .validate_all(&compilation.wasm_inner)
        .expect("normalized short-circuit AIR must emit valid wasm");
}

#[test]
fn named_constants_are_literal_patterns_and_guards_fall_through() {
    let source = r#"
module main;
const YES: bool = true;
fn classify(v: bool) -> i64 {
    match v {
        YES if false => { return 1; },
        _ => { return 2; }
    }
}
"#;
    let compilation =
        compile_named_module("const_guard.sigil", source).expect("constant pattern + guard");
    let classify = compilation
        .air
        .functions
        .iter()
        .find(|function| function.name.ends_with("classify"))
        .expect("classify AIR");
    assert!(
        classify
            .blocks
            .iter()
            .filter(|block| matches!(block.terminator, AirTerminator::Branch { .. }))
            .count()
            >= 2,
        "pattern test and guard must both be represented in AIR"
    );
}

#[test]
fn unsupported_named_constant_pattern_types_are_t277() {
    let source = r#"
module main;
const PI: f64 = 3.0;
fn classify(v: f64) -> i64 {
    match v {
        PI => { return 1; },
        _ => { return 0; }
    }
}
"#;
    assert!(codes(source).iter().any(|code| code == "T277"));
}

#[test]
fn an_unknown_pattern_identifier_remains_a_binding() {
    let source = r#"
module main;
fn identity(v: i64) -> i64 {
    match v {
        bound => { return bound; }
    }
}
"#;
    assert!(codes(source).is_empty());
}
