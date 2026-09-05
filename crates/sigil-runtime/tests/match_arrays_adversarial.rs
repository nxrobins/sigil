//! PR Phase-5 adversarial sweep — 41 fixtures (3-agent workflow), folded as a
//! permanent regression test. category: runtime (neg-sentinel K), accept (clean),
//! reject (diagnostic code present).
use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn wrap(body: &str) -> String {
    format!(
        "module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 {{
{body}
}}
"
    )
}

/// (category, body, expected)
const FIXTURES: &[(&str, &str, &str)] = &[
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [10, 20, 30]; match arr { [..x, ..y] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [10, 20, 30]; match arr { [..x, b] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 4] = [10, 20, 30, 40]; match arr { [a, ..r, b] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 2] = [10, 20]; match arr { [1, x] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 1] = [10]; match arr { [1..=3] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [bool; 1] = [true]; match arr { [true] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 2] = [10, 20]; match arr { [,] => { return 0 - 1; }, }"#,
        r#"P019"#,
    ),
    (
        r#"reject"#,
        r#"let x: i64 = 7; match x { [a] => { return 0 - 1; }, }"#,
        r#"T264"#,
    ),
    (
        r#"reject"#,
        r#"let t: (i64, i64) = (1, 2); match t { [a, b] => { return 0 - 1; }, }"#,
        r#"T264"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [10, 20, 30]; match arr { [a, b] => { return 0 - 1; }, }"#,
        r#"T265"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [10, 20, 30]; match arr { [a, b, c, d] => { return 0 - 1; }, }"#,
        r#"T265"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [10, 20, 30]; match arr { [a, b, c, d, ..r] => { return 0 - 1; }, }"#,
        r#"T265"#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 1] = [99]; match arr { [_] => { return 0; }, }"#,
        r#""#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 2] = [4, 5]; match arr { [a, b,] => { return a + b; }, }"#,
        r#""#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 3] = [7, 8, 9]; match arr { [a, ..rest,] => { return a; }, }"#,
        r#""#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 5] = [1, 2, 3, 4, 5]; match arr { [..] => { return 0; }, }"#,
        r#""#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    let s: &[i64] = &arr[0..3];
    match s {
        [] => { return 0; },
        [a] => { return a; },
        [a, ..rest] => { return a; },
    }"#,
        r#""#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 3] = [4, 5, 6];
    let s: &[i64] = &arr[0..3];
    match s {
        [a] => { return a; },
        [a, b] => { return a + b; },
        [..rest] => { return 0; },
    }"#,
        r#""#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    let s: &[i64] = &arr[0..3];
    match s {
        [] => { return 0; },
        [a, b, ..rest] => { return a; },
    }"#,
        r#"T088"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 2] = [7, 8];
    let s: &[i64] = &arr[0..2];
    match s {
        [head, ..tail] => { return head; },
    }"#,
        r#"T088"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 2] = [9, 10];
    let s: &[i64] = &arr[0..2];
    match s {
        [a] => { return a; },
    }"#,
        r#"T088"#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    match arr {
        [a, b, c] => { return a + b + c; },
    }"#,
        r#""#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    match arr {
        [a, b] => { return a + b; },
    }"#,
        r#"T265"#,
    ),
    (
        r#"accept"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    match arr {
        [a, ..rest] => { return a; },
    }"#,
        r#""#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    match arr {
        [a, b, c, d, ..rest] => { return a; },
    }"#,
        r#"T265"#,
    ),
    (
        r#"reject"#,
        r#"let arr: [i64; 3] = [1, 2, 3];
    match arr {
        [a, b, c] if a > 0 => { return a; },
    }"#,
        r#"T088"#,
    ),
    (
        r#"runtime"#,
        r#"let arr: [i64; 3] = [10, 20, 30];
    let s: &[i64] = &arr[0..3];
    match s {
        [] => { return 0 - 99; },
        [a, ..rest] => {
            let lu: u32 = rest.len();
            let l: i64 = lu.as_i64();
            return 0 - l;
        },
    }"#,
        r#"2"#,
    ),
    (
        r#"runtime"#,
        r#"let arr: [i64; 3] = [5, 6, 7];
    match arr {
        [a, ..rest] => { return 0 - rest[1]; },
    }"#,
        r#"7"#,
    ),
    (
        r#"runtime"#,
        r#"let arr: [i64; 1] = [42];
    let s: &[i64] = &arr[0..1];
    match s {
        [] => { return 0 - 1; },
        [a] => { return 0 - a; },
        [a, ..rest] => { return 0 - 1; },
    }"#,
        r#"42"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [u32; 4] = [1000, 2000, 3000, 4000];
    match arr {
        [a, ..r] => { let r0: u32 = r[0]; let r2: u32 = r[2]; let sm: u32 = r0 + r2; let si: i64 = sm.as_i64(); return 0 - si; },
    }"#,
        r#"6000"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [bool; 3] = [false, true, true];
    match arr {
        [a, ..r] => { let b0: bool = r[0]; let b1: bool = r[1]; let mut t0: i64 = 2; if b0 { t0 = 1; } else {} let mut t1: i64 = 2; if b1 { t1 = 1; } else {} let lu: u32 = r.len(); let l: i64 = lu.as_i64(); return 0 - (t0 * 100 + t1 * 10 + l); },
    }"#,
        r#"112"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 5] = [11, 22, 33, 44, 55];
    let s: &[i64] = &arr[0..5];
    match s {
        [] => { return 0 - 1; },
        [a] => { return 0 - 2; },
        [a, b] => { return 0 - 3; },
        [a, b, ..r] => { let r0: i64 = r[0]; let r2: i64 = r[2]; let lu: u32 = r.len(); let l: i64 = lu.as_i64(); return 0 - (r0 + r2 + l); },
    }"#,
        r#"91"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 5] = [1, 2, 3, 4, 5];
    match arr {
        [..rest] => { let r0: i64 = rest[0]; let r4: i64 = rest[4]; let lu: u32 = rest.len(); let l: i64 = lu.as_i64(); return 0 - (r0 + r4 + l); },
    }"#,
        r#"11"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 2] = [3, 4];
    match arr {
        [a, b, ..r] => { let lu: u32 = r.len(); let l: i64 = lu.as_i64(); return 0 - (a + b + l + 100); },
    }"#,
        r#"107"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 3] = [9, 8, 7];
    match arr {
        [a, ..] => { return 0 - a; },
    }"#,
        r#"9"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 1] = [77];
    match arr {
        [only] => { return 0 - only; },
    }"#,
        r#"77"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 6] = [1, 2, 3, 4, 5, 6];
    match arr {
        [a, b, c, d, e, f] => { return 0 - (a + b + c + d + e + f); },
    }"#,
        r#"21"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 2] = [7, 8];
    let s: &[i64] = &arr[0..2];
    match s {
        [a] => { return 0 - 1; },
        [a, b] => { return 0 - (a + b); },
        [..rest] => { return 0 - 999; },
    }"#,
        r#"15"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 5] = [10, 20, 30, 40, 50];
    let s: &[i64] = &arr[1..4];
    match s {
        [a, b, c] => { return 0 - (a + b + c); },
        [..r] => { return 0 - 1; },
    }"#,
        r#"90"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [i64; 7] = [0, 1, 2, 3, 4, 5, 6];
    let s: &[i64] = &arr[2..6];
    match s {
        [] => { return 0 - 1; },
        [first, ..rest] => { let r0: i64 = rest[0]; let r2: i64 = rest[2]; let lu: u32 = rest.len(); let l: i64 = lu.as_i64(); return 0 - (first + r0 + r2 + l); },
    }"#,
        r#"13"#,
    ),
    (
        r#"runtime"#,
        r#"    let arr: [str; 4] = ["x", "yy", "zzz", "wwww"];
    match arr {
        [h, ..r] => { let rl: str = r[2]; return 0 - (h.len() + rl.len()); },
    }"#,
        r#"5"#,
    ),
];

#[test]
fn pr_p5_adversarial_sweep() {
    let mut failures: Vec<String> = Vec::new();
    for (i, (cat, body, expected)) in FIXTURES.iter().enumerate() {
        let src = wrap(body);
        let compiled = compile_tool(&src);
        match *cat {
            "accept" => match compiled {
                Ok(_) => {}
                Err(e) => {
                    let codes: Vec<String> = e
                        .diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect();
                    failures.push(format!(
                        "[#{i} accept] expected CLEAN, got {codes:?}
  body: {body}"
                    ));
                }
            },
            "reject" => match compiled {
                Ok(_) => failures.push(format!(
                    "[#{i} reject] expected {expected}, but compiled CLEAN
  body: {body}"
                )),
                Err(e) => {
                    let codes: Vec<String> = e
                        .diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect();
                    if !codes.iter().any(|c| c == expected) {
                        failures.push(format!(
                            "[#{i} reject] expected {expected} present, got {codes:?}
  body: {body}"
                        ));
                    }
                }
            },
            "runtime" => match compiled {
                Err(e) => {
                    let codes: Vec<String> = e
                        .diagnostics()
                        .iter()
                        .map(|d| d.code().to_string())
                        .collect();
                    failures.push(format!(
                        "[#{i} runtime] COMPILE_ERR {codes:?}
  body: {body}"
                    ));
                }
                Ok(result) => {
                    match execute_ephemeral(
                        &result.wasm,
                        b"",
                        result.fuel_budget,
                        &IoGrants::none(),
                    ) {
                        Err(ToolError::Trapped { message }) => {
                            let p = "tool returned error (";
                            match message.find(p) {
                                Some(idx) => {
                                    let s = idx + p.len();
                                    let e = message[s..].find(')').unwrap();
                                    let got = &message[s..s + e];
                                    if got != *expected {
                                        failures.push(format!(
                                            "[#{i} runtime] expected K={expected}, got {got}
  body: {body}"
                                        ));
                                    }
                                }
                                None => {
                                    failures.push(format!("[#{i} runtime] no sentinel: {message}"))
                                }
                            }
                        }
                        other => failures.push(format!(
                            "[#{i} runtime] expected trap, got {other:?}
  body: {body}"
                        )),
                    }
                }
            },
            other => panic!("bad category {other}"),
        }
    }
    if !failures.is_empty() {
        panic!(
            "
{} of {} adversarial fixtures diverged:

{}
",
            failures.len(),
            FIXTURES.len(),
            failures.join(
                "

"
            )
        );
    }
}
