//! Untrusted compiler inputs run in a killable subprocess: a hang, panic or
//! stack overflow is a test failure, never an indefinitely stuck test runner.
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const DEADLINE: Duration = Duration::from_secs(10);

fn compile_bounded(source: &str) -> Vec<String> {
    compile_with_deadline(source, DEADLINE, false).unwrap()
}

fn compile_with_deadline(
    source: &str,
    deadline: Duration,
    stalled_worker: bool,
) -> Result<Vec<String>, String> {
    let dir = tempfile::tempdir().unwrap();
    let input = dir.path().join("input.sigil");
    let output = dir.path().join("result.json");
    let errors = dir.path().join("stderr.txt");
    std::fs::write(&input, source).unwrap();
    let mut child = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "frontend_case_child", "--nocapture"])
        .env("SIGIL_FRONTEND_TEST_INPUT", &input)
        .env("SIGIL_FRONTEND_TEST_OUTPUT", &output)
        .env(
            "SIGIL_FRONTEND_TEST_STALL",
            if stalled_worker { "1" } else { "0" },
        )
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(&errors).unwrap())
        .spawn()
        .unwrap();
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            assert!(
                status.success(),
                "compiler subprocess failed: {status}\n{}",
                std::fs::read_to_string(errors).unwrap()
            );
            return Ok(serde_json::from_slice(&std::fs::read(output).unwrap()).unwrap());
        }
        if start.elapsed() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            return Err(format!(
                "compiler exceeded {deadline:?}; subprocess killed and reaped"
            ));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn frontend_case_child() {
    let Ok(input) = std::env::var("SIGIL_FRONTEND_TEST_INPUT") else {
        return;
    };
    if std::env::var("SIGIL_FRONTEND_TEST_STALL").as_deref() == Ok("1") {
        std::thread::sleep(Duration::from_secs(60));
    }
    let source = std::fs::read_to_string(input).unwrap();
    let codes = std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(
            move || match sigil_compiler::compile_named_module("work_limit", source) {
                Ok(_) => Vec::new(),
                Err(error) => error
                    .diagnostics()
                    .iter()
                    .map(|d| d.code().as_str().to_owned())
                    .collect::<Vec<_>>(),
            },
        )
        .unwrap()
        .join()
        .unwrap();
    std::fs::write(
        std::env::var("SIGIL_FRONTEND_TEST_OUTPUT").unwrap(),
        serde_json::to_vec(&codes).unwrap(),
    )
    .unwrap();
}

#[test]
fn branching_generic_work_is_bounded() {
    let source = "module work_limit;
        record Left<T> { value: T }
        record Right<T> { value: T }
        fn boom<T>(x: T) -> i64 {
            let a = boom(Left { value: x });
            let b = boom(Right { value: x });
            return a + b;
        }
        pub fn tool_main() -> i64 { return boom(1); }";
    let codes = compile_bounded(source);
    assert!(
        codes.iter().any(|c| c == "T151"),
        "expected specialization budget rejection, got {codes:?}"
    );
}

#[test]
fn ordinary_generic_identity_is_accepted() {
    let codes = compile_bounded(
        "module work_limit; fn identity<T>(x:T)->T { return x; } pub fn tool_main()->i64 { return identity(42); }",
    );
    assert!(codes.is_empty(), "ordinary generic rejected: {codes:?}");
}

#[test]
fn growing_generic_type_is_bounded_before_mangling() {
    let codes = compile_bounded(
        "module work_limit;
        fn grow<T>(x:T)->i64 { return grow((x,x)); }
        pub fn tool_main()->i64 { return grow(1); }",
    );
    assert!(
        codes.iter().any(|c| c == "T151"),
        "expected type size rejection: {codes:?}"
    );
}

#[test]
fn branching_generic_methods_are_bounded() {
    let codes = compile_bounded(
        "module work_limit;
        record Left<T> { value:T }
        record Right<T> { value:T }
        record Cell<T> { value:T }
        impl Cell<T> {
            fn boom(self:Cell<T>)->i64 {
                let left = Cell { value:Left { value:self.value } };
                let right = Cell { value:Right { value:self.value } };
                return left.boom() + right.boom();
            }
        }
        pub fn tool_main()->i64 { let c = Cell { value:1 }; return c.boom(); }",
    );
    assert!(
        codes.iter().any(|c| c == "T151"),
        "expected method budget rejection: {codes:?}"
    );
}

#[test]
fn branching_generic_associated_functions_are_bounded() {
    let codes = compile_bounded(
        "module work_limit;
        record Left<T> { value:T }
        record Right<T> { value:T }
        record Box<T> { value:T }
        impl Box<T> {
            pub fn boom(x:T)->i64 {
                let a = Box::boom(Left { value:x });
                let b = Box::boom(Right { value:x });
                return a + b;
            }
        }
        pub fn tool_main()->i64 { return Box::boom(1); }",
    );
    assert!(
        codes.iter().any(|c| c == "T151"),
        "expected associated-function budget rejection: {codes:?}"
    );
}

fn alias_source(depth: usize, branching: bool) -> String {
    let mut source = String::from("module work_limit; type A0 = i64;\n");
    for n in 1..=depth {
        let prev = n - 1;
        let body = if branching {
            format!("(A{prev}, A{prev})")
        } else {
            format!("A{prev}")
        };
        source.push_str(&format!("type A{n} = {body};\n"));
    }
    source.push_str(&format!(
        "fn consume(x:A{depth})->i64 {{ return 1; }}\npub fn tool_main()->i64 {{ return 1; }}"
    ));
    source
}

#[test]
fn branching_alias_expansion_is_bounded() {
    let codes = compile_bounded(&alias_source(30, true));
    assert!(
        codes.iter().any(|c| c == "T151"),
        "expected alias size rejection: {codes:?}"
    );
}

#[test]
fn long_acyclic_alias_chain_is_bounded() {
    let codes = compile_bounded(&alias_source(5000, false));
    assert!(
        codes.iter().any(|c| c == "T151"),
        "expected alias depth rejection: {codes:?}"
    );
}

#[test]
fn ordinary_aliases_are_accepted() {
    for branching in [false, true] {
        let codes = compile_bounded(&alias_source(5, branching));
        assert!(codes.is_empty(), "ordinary aliases rejected: {codes:?}");
    }
}

#[test]
fn parser_and_lexer_adversarial_inputs_terminate() {
    for source in [
        "module work_limit; actor Calc { actor Init { fn init() {} } }".to_owned(),
        "module work_limit; actor Calc { fn init() {} }".to_owned(),
        format!(
            "module work_limit; fn f()->i64 {{ return {}1{}; }}",
            "(".repeat(5000),
            ")".repeat(5000)
        ),
        "é\u{00a0}\u{feff}💯".to_owned(),
    ] {
        assert!(!compile_bounded(&source).is_empty());
    }
}

#[test]
fn deadline_detector_kills_and_reaps_a_stalled_worker() {
    let result = compile_with_deadline("", Duration::from_millis(100), true);
    assert!(result.unwrap_err().contains("killed and reaped"));
}

#[test]
fn unicode_errors_cover_whole_codepoints() {
    let text = "é\u{00a0}\u{feff}💯";
    let sf = sigil_compiler::source::SourceFile::new("unicode", text);
    let (_, diagnostics) = sigil_compiler::lexer::lex(&sf);
    assert_eq!(diagnostics.len(), text.chars().count());
    for (d, (start, ch)) in diagnostics.iter().zip(text.char_indices()) {
        let span = d.span().unwrap();
        assert_eq!((span.start, span.end), (start, start + ch.len_utf8()));
        assert_eq!(sf.span_text(span), ch.to_string());
        sf.line_col(span.start);
        sf.line_col(span.end);
    }
}

#[test]
fn long_flat_operator_chain_is_bounded() {
    let source = format!(
        "module work_limit; pub fn tool_main()->i64 {{ return {}1; }}",
        "1+".repeat(10000)
    );
    let codes = compile_bounded(&source);
    assert!(
        codes.iter().any(|c| c == "S007"),
        "expected AST depth rejection: {codes:?}"
    );
}

#[test]
fn long_flat_postfix_chain_is_bounded() {
    let source = format!(
        "module work_limit;
        record R {{ x:i64 }}
        impl R {{ pub fn id(self:R)->R {{ return self; }} }}
        fn make()->R {{ return R {{ x:1 }}; }}
        pub fn tool_main()->i64 {{ return make(){}.x; }}",
        ".id()".repeat(10000)
    );
    let codes = compile_bounded(&source);
    assert!(
        codes.iter().any(|c| c == "S007"),
        "expected AST depth rejection: {codes:?}"
    );
}

fn balanced_sum(leaves: usize) -> String {
    if leaves == 1 {
        "1".to_owned()
    } else {
        let left = leaves / 2;
        let right = leaves - left;
        format!("({}+{})", balanced_sum(left), balanced_sum(right))
    }
}

#[test]
fn wide_shallow_expression_remains_accepted() {
    let source = format!(
        "module work_limit; pub fn tool_main()->i64 {{ return {}; }}",
        balanced_sum(512)
    );
    let codes = compile_bounded(&source);
    assert!(
        codes.is_empty(),
        "wide shallow expression rejected: {codes:?}"
    );
}
