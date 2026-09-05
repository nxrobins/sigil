//! Iterator protocol PR-2: `for x in v.iter()` over a real `Vec<i64>`. Exercises
//! vec.sigil's new `VecIter` / `Vec::iter` surface, the ambient `option` edge (the
//! vec trigger must pull `option` since `VecIter::next` returns `Option<T>` and the
//! scanner never sees vec.sigil's own `Some`/`None`), and the PR-1 for-in desugar —
//! all together, with NO explicit `use`. The tool is `! { Alloc }` (the Vec allocates;
//! `iter`/`next` themselves are Alloc-free).

use sigil_compiler::compile_tool;
use sigil_runtime::ephemeral::ToolError;
use sigil_runtime::execute_ephemeral;
use sigil_runtime::grants::IoGrants;

fn tool(body: &str) -> String {
    format!(
        "module tool;\npub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! {{ Alloc }} {{\n{body}\n}}\n"
    )
}

fn neg(body: &str) -> i64 {
    let result = compile_tool(&tool(body)).expect("tool should compile");
    match execute_ephemeral(&result.wasm, b"", result.fuel_budget, &IoGrants::none()) {
        Err(ToolError::Trapped { message }) => {
            let prefix = "tool returned error (";
            let start = message.find(prefix).unwrap_or_else(|| {
                panic!("expected a clean negative-sentinel return, got a genuine trap: {message}")
            }) + prefix.len();
            let end = message[start..]
                .find(')')
                .unwrap_or_else(|| panic!("malformed trap: {message}"));
            message[start..start + end]
                .parse::<i64>()
                .unwrap_or_else(|e| panic!("can't parse trap code from {message:?}: {e}"))
        }
        Err(other) => panic!("tool failed with non-trap error: {other:?}"),
        Ok(_) => panic!("tool returned a positive packed-pointer; expected negative sentinel"),
    }
}

/// `let mut v = Vec::new(); v.push(1)..v.push(n)`.
fn fill(n: i64) -> String {
    let mut s = String::from("    let mut v: Vec<i64> = Vec::new();\n");
    for k in 1..=n {
        s.push_str(&format!("    v.push({k});\n"));
    }
    s
}

#[test]
fn for_in_vec_iter_sums() {
    // 1+2+3+4+5 = 15.
    let body = format!(
        "{}    let mut sum: i64 = 0;\n    for x in v.iter() {{\n        sum = sum + x;\n    }}\n    return 0 - sum;",
        fill(5)
    );
    assert_eq!(neg(&body), 15);
}

#[test]
fn for_in_empty_vec_iter_zero_iterations() {
    let body = "    let mut v: Vec<i64> = Vec::new();\n\
        \x20   let mut sum: i64 = 0;\n\
        \x20   for x in v.iter() {\n\
        \x20       sum = sum + x + 1000;\n\
        \x20   }\n\
        \x20   return 0 - (sum + 7);";
    assert_eq!(neg(body), 7); // sum 0
}

#[test]
fn for_in_vec_iter_preserves_order() {
    // get(0)=10, then 20, 30 → encode the FIRST element seen times 100 + count.
    let body = format!(
        "{}    let mut first: i64 = 0 - 1;\n    let mut count: i64 = 0;\n    for x in v.iter() {{\n        if count == 0 {{ first = x; }} else {{ }}\n        count = count + 1;\n    }}\n    return 0 - (first * 10 + count);",
        "    let mut v: Vec<i64> = Vec::new();\n    v.push(10);\n    v.push(20);\n    v.push(30);\n"
    );
    // first=10, count=3 → 10*10 + 3 = 103.
    assert_eq!(neg(&body), 103);
}

#[test]
fn vec_iter_next_directly() {
    // Drive the iterator by hand (no for-loop): two next() calls advance 1 → 2.
    let body = format!(
        "{}    let mut it: VecIter<i64> = v.iter();\n    let o1: Option<i64> = it.next();\n    let o2: Option<i64> = it.next();\n    return 0 - (o1.unwrap_or(0) * 100 + o2.unwrap_or(0));",
        fill(3)
    );
    // o1=1, o2=2 → 1*100 + 2 = 102.
    assert_eq!(neg(&body), 102);
}
