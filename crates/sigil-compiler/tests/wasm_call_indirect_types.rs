//! `call_indirect` type entries for signatures no function of the module carries.
//!
//! `wasm::emit` looked a `call_indirect`'s type up among the module's own function types, which
//! hold a closure signature only when the module lambda-lifts a closure of it. A module that calls
//! a closure-typed parameter and builds no closure of that signature (the closure is in the other
//! ring's module, inside a generic nobody instantiates, or nowhere) passed every checker and then
//! panicked in the backend with `ICE: call_indirect signature not found in type map: [I32, I64]
//! -> [I64]`, on a two-line program. Emission now registers the signature of every `CallIndirect`
//! before emitting code: each one no function carries is appended after the function types, once,
//! in AIR order. A module whose indirect signatures all belong to its functions gains no entry and
//! keeps its bytes.
//!
//! Pinned here from source, in both rings: the module compiles and validates, and its
//! `call_indirect` names a type entry equal to the call site's signature, appended right after the
//! function types. Several missing signatures are appended once each, in the order the AIR first
//! calls them. The control builds its closure locally, and the same reader finds nothing appended:
//! the scan adds only what is missing. Running the repaired modules is `sigil-runtime`'s half
//! (`tests/call_indirect_types_run.rs`).

use sigil_compiler::compile_module;
use sigil_compiler::compiler::Compilation;
use wasmparser::{Operator, Parser, Payload, TypeRef, ValType};

/// The reported program: it calls its closure-typed parameter and builds no closure.
const CLOSURE_PARAM: &str = "module m;\npub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n";

/// The same module in the outer ring, which production emits as the second (outer) module.
const CLOSURE_PARAM_OUTER: &str =
    "#[ring(outer)]\nmodule m;\npub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n";

/// Three closure-typed parameters, two of one signature, called in the order g, f, k.
const THREE_CALLS: &str = "module m;\n\
    pub fn pick(f: Fn(i64) -> i64, g: Fn(i64, i64) -> bool, k: Fn(i64) -> i64) -> i64 { \
    if g(1, 2) { return f(3); } return k(4); }\n";

/// The control: the module lifts a closure of the signature it calls.
const LOCAL_CLOSURE: &str = "module m;\n\
    pub fn h(f: Fn(i64) -> i64) -> i64 { return f(42); }\n\
    pub fn g() -> i64 { return h(fn(x: i64) -> i64 { return x + 1; }); }\n";

/// A wasm function signature: (params, results).
type Signature = (Vec<ValType>, Vec<ValType>);

/// The signature of `Fn(i64) -> i64`'s call site: the closure's environment pointer, then the
/// argument.
fn env_i64_to_i64() -> Signature {
    (vec![ValType::I32, ValType::I64], vec![ValType::I64])
}

/// What the checks read from an emitted module.
struct Shape {
    /// Every type entry, in index order.
    types: Vec<Signature>,
    /// Function imports, runtime and ffi: one type entry each, ahead of the function types.
    imports: usize,
    /// Defined functions: one type entry each, after the imports' entries.
    functions: usize,
    /// The type index of every `call_indirect`, in code-section order.
    indirect: Vec<u32>,
}

impl Shape {
    /// The type entries after the function types: the signatures emission appended because no
    /// function of the module carries them.
    fn appended(&self) -> &[Signature] {
        &self.types[self.imports + self.functions..]
    }

    /// The index the first appended entry takes.
    fn first_appended_index(&self) -> u32 {
        (self.imports + self.functions) as u32
    }
}

fn compile(src: &str) -> Compilation {
    compile_module(src).unwrap_or_else(|err| panic!("the program is accepted: {err:?}"))
}

/// Read `bytes` after validating them. Fails closed on the layout `appended` relies on: import
/// `i` must declare type `i` and function `j` type `imports + j`, so every entry past those is one
/// that no import or function declares.
fn shape(bytes: &[u8]) -> Shape {
    wasmparser::validate(bytes).expect("the emitted module validates");
    let mut types = Vec::new();
    let mut import_types = Vec::new();
    let mut function_types = Vec::new();
    let mut indirect = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("valid wasm") {
            Payload::TypeSection(reader) => {
                types = reader
                    .into_iter_err_on_gc_types()
                    .map(|ty| {
                        let ty = ty.expect("an ordinary function type");
                        (ty.params().to_vec(), ty.results().to_vec())
                    })
                    .collect();
            }
            Payload::ImportSection(reader) => {
                for import in reader.into_imports() {
                    if let TypeRef::Func(index) = import.expect("valid import").ty {
                        import_types.push(index);
                    }
                }
            }
            Payload::FunctionSection(reader) => {
                function_types = reader
                    .into_iter()
                    .collect::<Result<_, _>>()
                    .expect("valid function section");
            }
            Payload::CodeSectionEntry(body) => {
                let mut reader = body.get_operators_reader().expect("valid body");
                while !reader.eof() {
                    if let Operator::CallIndirect { type_index, .. } =
                        reader.read().expect("valid operator")
                    {
                        indirect.push(type_index);
                    }
                }
            }
            _ => {}
        }
    }
    let (imports, functions) = (import_types.len(), function_types.len());
    assert_eq!(
        import_types,
        (0..imports as u32).collect::<Vec<_>>(),
        "import i declares type entry i"
    );
    assert_eq!(
        function_types,
        (imports as u32..(imports + functions) as u32).collect::<Vec<_>>(),
        "function j declares type entry imports + j"
    );
    Shape {
        types,
        imports,
        functions,
        indirect,
    }
}

/// REGRESSION: the reported program compiles, and its single `call_indirect` names the one
/// appended entry, which is the call site's signature.
#[test]
fn closure_parameter_call_compiles_and_names_its_appended_signature() {
    let compilation = compile(CLOSURE_PARAM);
    assert!(
        compilation.wasm_outer.is_none(),
        "a single-ring program emits one module"
    );
    let shape = shape(&compilation.wasm_inner);
    assert_eq!(shape.functions, 1, "`h` is the only function");
    assert_eq!(shape.appended(), [env_i64_to_i64()]);
    assert_eq!(shape.indirect, vec![shape.first_appended_index()]);
}

/// REGRESSION, outer ring: the call site is in the outer module, whose reduced import set puts
/// the function types at a different offset; the entry is appended there. The inner module holds
/// no function, so it has no call site and nothing appended.
#[test]
fn outer_ring_closure_parameter_call_compiles_and_names_its_appended_signature() {
    let compilation = compile(CLOSURE_PARAM_OUTER);
    let outer = shape(
        compilation
            .wasm_outer
            .as_deref()
            .expect("an outer-ring program emits an outer module"),
    );
    assert_eq!(outer.functions, 1, "`h` is the only outer function");
    assert_eq!(outer.appended(), [env_i64_to_i64()]);
    assert_eq!(outer.indirect, vec![outer.first_appended_index()]);
    let inner = shape(&compilation.wasm_inner);
    assert_eq!(inner.functions, 0);
    assert!(inner.indirect.is_empty() && inner.appended().is_empty());
}

/// Each missing signature is appended once, in the order the AIR first calls it: `g`'s
/// `(env, i64, i64) -> bool` (a `bool` is an `i32`), then the `(env, i64) -> i64` that `f` and
/// `k` share.
#[test]
fn missing_signatures_are_appended_once_each_in_call_order() {
    let shape = shape(&compile(THREE_CALLS).wasm_inner);
    let g = (
        vec![ValType::I32, ValType::I64, ValType::I64],
        vec![ValType::I32],
    );
    assert_eq!(shape.appended(), [g, env_i64_to_i64()]);
    let first = shape.first_appended_index();
    assert_eq!(shape.indirect, vec![first, first + 1, first + 1]);
}

/// The control: a module that lifts a closure of the signature it calls carries it as that
/// closure's function type, and the `call_indirect` names that entry. Nothing is appended: the
/// type section is the imports' and functions' entries alone. The same reader reports the appended
/// entry in the regressions above, so its empty answer here is a measurement.
#[test]
fn a_locally_lifted_closure_serves_the_call_and_nothing_is_appended() {
    let shape = shape(&compile(LOCAL_CLOSURE).wasm_inner);
    assert!(
        shape.appended().is_empty(),
        "the scan appends only what is missing"
    );
    assert_eq!(shape.indirect.len(), 1);
    let named = shape.indirect[0] as usize;
    assert!(
        (shape.imports..shape.imports + shape.functions).contains(&named),
        "the call names a function's own type entry"
    );
    assert_eq!(shape.types[named], env_i64_to_i64());
}
