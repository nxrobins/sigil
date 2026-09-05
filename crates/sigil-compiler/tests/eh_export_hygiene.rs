//! EH4.3 export-hygiene regression: a `pub` abortive-propagation CHAIN function has its
//! ABI rewritten by the evidence-passing desugar (return type → `$EhResult$<H>`, plus an
//! evidence parameter). Its wasm export MUST NOT advertise that mutated ABI under the
//! original public symbol (a footgun if anything ever resolves imports by export name).

use wasmparser::{Parser, Payload};

/// Map every EXPORTED function to its (param_count, result_count), by walking the type /
/// function / import / export sections of the compiled module.
fn exported_fn_arities(wasm: &[u8]) -> std::collections::BTreeMap<String, (usize, usize)> {
    let mut types: Vec<(usize, usize)> = Vec::new(); // (params, results) per type index
    let mut fn_type_idx: Vec<u32> = Vec::new(); // defined-function → type index
    let mut imported_fns: u32 = 0;
    let mut exports: Vec<(String, u32)> = Vec::new(); // (name, function index)

    for payload in Parser::new(0).parse_all(wasm) {
        match payload.expect("valid wasm payload") {
            Payload::TypeSection(reader) => {
                for rg in reader {
                    let rg = rg.expect("type");
                    for ty in rg.into_types() {
                        if let wasmparser::CompositeInnerType::Func(f) = ty.composite_type.inner {
                            types.push((f.params().len(), f.results().len()));
                        } else {
                            types.push((0, 0));
                        }
                    }
                }
            }
            Payload::ImportSection(reader) => {
                for imp in reader.into_imports() {
                    if matches!(imp.expect("import").ty, wasmparser::TypeRef::Func(_)) {
                        imported_fns += 1;
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                for ti in reader {
                    fn_type_idx.push(ti.expect("func type idx"));
                }
            }
            Payload::ExportSection(reader) => {
                for ex in reader {
                    let ex = ex.expect("export");
                    if ex.kind == wasmparser::ExternalKind::Func {
                        exports.push((ex.name.to_owned(), ex.index));
                    }
                }
            }
            _ => {}
        }
    }

    exports
        .into_iter()
        .filter_map(|(name, idx)| {
            // Only defined functions (idx >= imported) have a body/type here.
            let defined = idx.checked_sub(imported_fns)? as usize;
            let tyidx = *fn_type_idx.get(defined)? as usize;
            Some((name, types[tyidx]))
        })
        .collect()
}

const CHAIN: &str = "#[ring(outer)]\nmodule tool;\n\
    effect Fail { fn raise() -> never; }\n\
    pub fn deep(x: i64) -> i64 ! { Fail } { if x < 0 { perform Fail.raise(); } return x; }\n\
    fn mid(x: i64) -> i64 ! { Fail } { return deep(x); }\n\
    pub fn tool_main(i: i64, l: i64) -> i64 { let r = handle mid(i) { Fail.raise() => 7 }; return r; }\n";

#[test]
fn rewritten_pub_chain_fn_does_not_export_a_mutated_abi() {
    let compiled = sigil_compiler::compile_tool(CHAIN).expect("compiles");
    let arities = exported_fn_arities(&compiled.wasm);

    // `deep` is rewritten to `(i64, $ev) -> $EhResult$i64` (2 params). Its original public
    // symbol `tool__deep` must NOT be exported with that mutated ABI. The desugar marks
    // rewritten chain functions internal (a `$`-prefixed export name), so they are dropped
    // from the public export section entirely — exactly like the `$eh_clause` closures.
    assert!(
        !arities.contains_key("tool__deep"),
        "rewritten chain fn `tool__deep` must not be exported (its declared ABI is \
         (i64)->i64 but the lowering rewrote it to (i64,$ev)->$EhResult). exports: {arities:?}"
    );
    // No exported function may carry the synthesized `$`-internal naming either.
    assert!(
        arities.keys().all(|n| !n.starts_with('$')),
        "no `$`-prefixed compiler-internal function should be exported. exports: {arities:?}"
    );
    // The real entry is still exported with its declared ABI.
    assert_eq!(
        arities.get("tool__tool_main"),
        Some(&(2usize, 1usize)),
        "tool_main must still be exported with its declared (i64,i64)->i64 ABI. exports: {arities:?}"
    );
}

#[test]
fn private_source_helpers_are_callable_internally_but_not_wasm_exports() {
    let source = r#"
module export_policy;
fn helper(x: i64) -> i64 { return x + 1; }
pub fn invoke(x: i64) -> i64 { return helper(x); }
"#;
    let compiled = sigil_compiler::compile_module(source).expect("module compiles");
    let arities = exported_fn_arities(&compiled.wasm_inner);

    assert!(
        !arities.contains_key("export_policy__helper"),
        "a private helper must not become an externally callable root: {arities:?}"
    );
    assert_eq!(
        arities.get("export_policy__invoke"),
        Some(&(1usize, 1usize)),
        "the declared public entry must retain its external ABI: {arities:?}"
    );
}
