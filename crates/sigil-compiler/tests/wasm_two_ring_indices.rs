//! P2B-TWORING — per-ring wasm function indices.
//!
//! `wasm::emit` splits a two-ring program into an inner and an outer module, each numbering
//! its functions by position in ITS ring's slice, while `AirStmt::Call` names the GLOBAL
//! `FuncId` (position in the whole program) and a closure stores its global id as its
//! `call_indirect` table slot. Emission used `import_count + FuncId` as the call index and a
//! compact per-ring table, which is right only when the callee's ring happens to occupy the
//! global prefix (an outer-first layout). With an inner module first — the natural layout,
//! since inner is the default ring — every outer->outer call pointed at the wrong outer
//! function: a same-signature neighbour VALIDATES and runs (a tool invoking a function the
//! source never named); any other shape fails to instantiate or traps. The closure table had
//! the same defect: a stored global id selected a different same-signature closure.
//!
//! The fix keeps the AIR untouched (one numbering, the global `FuncId`) and lives in the
//! emitter: direct calls go through a per-ring `FuncId -> index` map, and the table spans the
//! whole program's ids with each ring placing its own functions at their global slots.
//!
//! The checkers here decode the emitted bodies and element segments with `wasmparser` and
//! compare them with what the AIR names under the partition rule, for both layouts. The SC-P4
//! anti-stubs plant the old formulas into the FIXED bytes (the old call index at the exact call
//! site; the old compact table), show the wasm validator accepts both, and show the checkers
//! reject both.
//!
//! ROUND 2. The first pass asserted that a callee outside this ring's module could only come
//! from a program `ring_check` had already rejected (R004), and panicked. That premise was
//! FALSE: `type_check` files a monomorphized generic instance under `modules[0]`, so in a
//! two-ring program an instance inherits the first module's ring instead of its definer's, and
//! a generic defined and called inside ONE ring lowers to a cross-ring call from a source that
//! contains none. Round 1 missed it because the cross-ring test hand-rewrote an AIR `Call` —
//! a shape no source produces — so the source path was never exercised. The gate is now
//! `ring_check::check_air_ring_placement` (R007, over the exact AIR `emit` receives) and the
//! emitter's panic is its backstop; the tests below drive the generic shape from SOURCE in both
//! layouts and pin the control that must keep compiling.

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use sigil_compiler::air::{AirFunction, AirFunctionKind, AirProgram, AirStmt, AirValue, FuncId};
use sigil_compiler::ast::Ring;
use sigil_compiler::compile_module;
use sigil_compiler::compiler::Compilation;
use sigil_compiler::ring_check;
use sigil_compiler::wasm;
use wasmparser::{ElementItems, ElementKind, ExternalKind, Operator, Parser, Payload, TypeRef};

// ── fixtures ─────────────────────────────────────────────────────────────────────────────────

/// Inner module FIRST; the outer tool calls an outer helper. Global ids: dummy=0, helper=1,
/// tool_main=2. Outer-local: helper=2, tool_main=3. The old formula emitted `call 3` (itself).
const INNER_FIRST: &str = "module first;\n\
    fn dummy() -> i64 { return 0; }\n\
    #[ring(outer)]\nmodule tool;\n\
    fn helper(x: i64) -> i64 { return x + 40; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return helper(2); }\n";

/// The same program with the modules swapped: the outer ring occupies the global prefix, so
/// the old formula was right by coincidence.
const OUTER_FIRST: &str = "#[ring(outer)]\nmodule tool;\n\
    fn helper(x: i64) -> i64 { return x + 40; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return helper(2); }\n\
    module first;\n\
    fn dummy() -> i64 { return 0; }\n";

/// The mirror: outer module FIRST, an inner tool calls an inner helper. Inner-local: helper=8,
/// tool_main=9; the old formula emitted `call 9` (itself).
const INNER_CALLS_OUTER_FIRST: &str = "#[ring(outer)]\nmodule tool;\n\
    fn dummy() -> i64 { return 0; }\n\
    module app;\n\
    fn helper(x: i64) -> i64 { return x + 40; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return helper(2); }\n";

/// The mirror's twin with the inner module first.
const INNER_CALLS_INNER_FIRST: &str = "module app;\n\
    fn helper(x: i64) -> i64 { return x + 40; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return helper(2); }\n\
    #[ring(outer)]\nmodule tool;\n\
    fn dummy() -> i64 { return 0; }\n";

/// The security-relevant shape: two outer functions with the SAME signature. Global ids:
/// dummy=0, plus_one=1, times_hundred=2, tool_main=3; outer-local: plus_one=2,
/// times_hundred=3, tool_main=4. The old formula emitted `call 3` = `times_hundred`, which
/// validates and returns 100 where the source names `plus_one(1)` = 2.
const COLLISION: &str = "module first;\n\
    fn dummy() -> i64 { return 0; }\n\
    #[ring(outer)]\nmodule tool;\n\
    fn plus_one(x: i64) -> i64 { return x + 1; }\n\
    fn times_hundred(x: i64) -> i64 { return x * 100; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return plus_one(1); }\n";

/// A closure in the outer ring with TWO inner functions first: the closure's global id (3)
/// indexed past the old two-entry outer table (trap).
const CLOSURE: &str = "module first;\n\
    fn dummy() -> i64 { return 0; }\n\
    fn dummy2() -> i64 { return 1; }\n\
    #[ring(outer)]\nmodule tool;\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { \
        let f = fn(x: i64) -> i64 { return x + 1; }; return f(41); }\n";

/// The closure-table collision: two outer closures of the same wasm signature. Global ids:
/// dummy=0, tool_main=1, a=2, b=3. The old compact outer table held [tool_main, a, b] at
/// slots 0..3, so `a`'s stored id 2 selected `b`: `call_indirect` validated, type-checked, and
/// returned 100 where the source names `a(1)` = 2.
const CLOSURE_COLLISION: &str = "module first;\n\
    fn dummy() -> i64 { return 0; }\n\
    #[ring(outer)]\nmodule tool;\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { \
        let a = fn(x: i64) -> i64 { return x + 1; }; \
        let b = fn(x: i64) -> i64 { return x * 100; }; return a(1); }\n";

/// Actor handlers are inner-only; with an outer module FIRST the handler's call to an inner
/// helper was emitted as a self-call.
const ACTOR: &str = "#[ring(outer)]\nmodule tool;\n\
    fn dummy() -> i64 { return 0; }\n\
    module app;\n\
    fn helper(x: i64) -> i64 { return x + 40; }\n\
    entry actor Main {\n\
      on Start() -> i64 { return helper(2); }\n\
    }\n";

/// ROUND 2. Inner module FIRST; the outer tool calls an outer GENERIC helper. The source has
/// NO cross-ring call (`ident` is declared and called inside `tool`), but `type_check` files a
/// monomorphized instance under `modules[0]` = `first`, so `tool::ident__i64` is lowered with
/// the INNER ring and the call crosses the boundary in AIR. `main` compiles this and emits a
/// module whose call index is misdirected; round 1 turned it into an ICE.
const GENERIC_INNER_FIRST: &str = "module first;\n\
    fn dummy() -> i64 { return 0; }\n\
    #[ring(outer)]\nmodule tool;\n\
    fn ident<T>(x: T) -> T { return x; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return ident(42); }\n";

/// ROUND 2, the mirror: outer module FIRST, an inner tool calls an inner GENERIC helper. The
/// instance is filed under the OUTER `modules[0]`, so the call crosses the other way.
const GENERIC_OUTER_FIRST_MIRROR: &str = "#[ring(outer)]\nmodule tool;\n\
    fn dummy() -> i64 { return 0; }\n\
    module app;\n\
    fn ident<T>(x: T) -> T { return x; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return ident(42); }\n";

/// ROUND 2 control: the SAME program as `GENERIC_INNER_FIRST` with the generic's module
/// declared first, so `modules[0]` is the definer and the instance lands in its own ring. This
/// is the workaround the R007 hint names, and it must keep compiling.
const GENERIC_DEFINER_FIRST: &str = "#[ring(outer)]\nmodule tool;\n\
    fn ident<T>(x: T) -> T { return x; }\n\
    pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 { return ident(42); }\n\
    module app;\n\
    fn dummy() -> i64 { return 0; }\n";

// ── the checkers ─────────────────────────────────────────────────────────────────────────────

fn compile(src: &str) -> Compilation {
    compile_module(src).unwrap_or_else(|err| panic!("fixture must compile: {err:?}"))
}

fn module_bytes(compilation: &Compilation, ring: Ring) -> &[u8] {
    match ring {
        Ring::Inner => &compilation.wasm_inner,
        Ring::Outer => compilation
            .wasm_outer
            .as_deref()
            .expect("a two-ring fixture emits an outer module"),
    }
}

/// The partition `wasm::emit` uses: `ring`'s functions in program order with their global ids.
fn ring_partition(air: &AirProgram, ring: Ring) -> Vec<(FuncId, &AirFunction)> {
    air.functions
        .iter()
        .enumerate()
        .filter(|(_, f)| f.ring == ring)
        .map(|(index, f)| (FuncId(index as u32), f))
        .collect()
}

fn global_id(air: &AirProgram, name: &str) -> u32 {
    air.functions
        .iter()
        .position(|f| f.name == name)
        .unwrap_or_else(|| panic!("`{name}` is lowered")) as u32
}

/// Function imports precede defined functions in the wasm function index space.
fn import_count(bytes: &[u8]) -> u32 {
    let mut count = 0;
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::ImportSection(section) = payload.expect("valid wasm") {
            for import in section.into_imports() {
                if matches!(import.expect("valid import").ty, TypeRef::Func(_)) {
                    count += 1;
                }
            }
        }
    }
    count
}

fn exports(bytes: &[u8]) -> Vec<(String, u32)> {
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::ExportSection(section) = payload.expect("valid wasm") {
            for export in section {
                let export = export.expect("valid export");
                if export.kind == ExternalKind::Func {
                    out.push((export.name.to_owned(), export.index));
                }
            }
        }
    }
    out
}

/// Per defined function, in code-section order: every direct `call` target that is a defined
/// function of this module (imports — runtime and ffi — are below `import_count`), sorted.
fn emitted_user_calls(bytes: &[u8]) -> Vec<Vec<u32>> {
    let imports = import_count(bytes);
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CodeSectionEntry(body) = payload.expect("valid wasm") {
            let mut reader = body.get_operators_reader().expect("valid body");
            let mut calls = Vec::new();
            while !reader.eof() {
                if let Operator::Call { function_index } = reader.read().expect("valid operator")
                    && function_index >= imports
                {
                    calls.push(function_index);
                }
            }
            calls.sort_unstable();
            out.push(calls);
        }
    }
    out
}

/// Per function of `ring`, in partition order: the call indices the AIR names, resolved by
/// the partition rule `import_count + position of the callee in this ring's slice`, sorted. A
/// callee outside the ring resolves to `None` (the checker reports it as misdirected).
fn expected_user_calls(air: &AirProgram, ring: Ring, imports: u32) -> Vec<Vec<Option<u32>>> {
    let partition = ring_partition(air, ring);
    partition
        .iter()
        .map(|(_, function)| {
            let mut calls: Vec<Option<u32>> = function
                .blocks
                .iter()
                .flat_map(|block| block.stmts.iter())
                .filter_map(|stmt| match stmt {
                    AirStmt::Call { func, .. } => Some(
                        partition
                            .iter()
                            .position(|(id, _)| id == func)
                            .map(|position| imports + position as u32),
                    ),
                    _ => None,
                })
                .collect();
            calls.sort_unstable();
            calls
        })
        .collect()
}

/// Every function of `ring` whose emitted direct calls differ from the callees the AIR names:
/// `(function name, emitted, expected)`.
fn misdirected_calls(
    bytes: &[u8],
    air: &AirProgram,
    ring: Ring,
) -> Vec<(String, Vec<u32>, Vec<u32>)> {
    let partition = ring_partition(air, ring);
    let emitted = emitted_user_calls(bytes);
    let expected = expected_user_calls(air, ring, import_count(bytes));
    assert_eq!(
        emitted.len(),
        partition.len(),
        "the module defines exactly the ring's functions"
    );
    partition
        .iter()
        .zip(emitted)
        .zip(expected)
        .filter_map(|(((_, function), emitted), expected)| {
            let expected: Vec<u32> = expected
                .into_iter()
                .map(|e| e.unwrap_or(u32::MAX))
                .collect();
            (emitted != expected).then(|| (function.name.clone(), emitted, expected))
        })
        .collect()
}

/// The wasm index of the ring's function named `name`, by the partition rule.
fn index_of(air: &AirProgram, ring: Ring, imports: u32, name: &str) -> u32 {
    let position = ring_partition(air, ring)
        .iter()
        .position(|(_, f)| f.name == name)
        .unwrap_or_else(|| panic!("`{name}` is in the {ring:?} ring"));
    imports + position as u32
}

/// The module's single funcref table: `(size, slot -> function index)` decoded from the
/// table and element sections. Slots no active segment covers are absent (uninitialized).
fn table_layout(bytes: &[u8]) -> (u64, Vec<(u32, u32)>) {
    let mut sizes = Vec::new();
    let mut slots = Vec::new();
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("valid wasm") {
            Payload::TableSection(section) => {
                for table in section {
                    sizes.push(table.expect("valid table").ty.initial);
                }
            }
            Payload::ElementSection(section) => {
                for element in section {
                    let element = element.expect("valid element");
                    let ElementKind::Active { offset_expr, .. } = element.kind else {
                        panic!("the emitter writes active segments only");
                    };
                    let mut offset_reader = offset_expr.get_operators_reader();
                    let Operator::I32Const { value: offset } =
                        offset_reader.read().expect("valid const expr")
                    else {
                        panic!("the emitter writes `i32.const` offsets only");
                    };
                    let ElementItems::Functions(items) = element.items else {
                        panic!("the emitter writes function-index items only");
                    };
                    for (position, item) in items.into_iter().enumerate() {
                        slots.push((offset as u32 + position as u32, item.expect("valid item")));
                    }
                }
            }
            _ => {}
        }
    }
    assert_eq!(sizes.len(), 1, "exactly one table");
    slots.sort_unstable();
    (sizes[0], slots)
}

/// Every function of `ring` whose table slot (its GLOBAL id, the value a closure stores) does
/// not hold its own wasm index, plus every initialized slot that is not one of the ring's
/// ids: `(function name or "<foreign slot>", slot, actual, expected)`. The table must also
/// span every global id (a stored id past the table traps rather than dispatches).
fn misplaced_table_slots(
    bytes: &[u8],
    air: &AirProgram,
    ring: Ring,
) -> Vec<(String, u32, Option<u32>, Option<u32>)> {
    let partition = ring_partition(air, ring);
    let imports = import_count(bytes);
    let (size, slots) = table_layout(bytes);
    let mut out = Vec::new();
    if size != air.functions.len() as u64 {
        out.push((
            "<table size>".to_owned(),
            size as u32,
            None,
            Some(air.functions.len() as u32),
        ));
    }
    for (position, (id, function)) in partition.iter().enumerate() {
        let expected = imports + position as u32;
        let actual = slots
            .iter()
            .find(|(slot, _)| *slot == id.0)
            .map(|(_, f)| *f);
        if actual != Some(expected) {
            out.push((function.name.clone(), id.0, actual, Some(expected)));
        }
    }
    for (slot, actual) in &slots {
        if !partition.iter().any(|(id, _)| id.0 == *slot) {
            out.push(("<foreign slot>".to_owned(), *slot, Some(*actual), None));
        }
    }
    out
}

/// The `__closure_id` values `function` stores (one per closure construction), in order.
fn stored_closure_ids(function: &AirFunction) -> Vec<i64> {
    function
        .blocks
        .iter()
        .flat_map(|block| block.stmts.iter())
        .filter_map(|stmt| match stmt {
            AirStmt::Assign {
                dst,
                val: AirValue::IntLit(value),
            } if function.debug_names.get(dst).map(String::as_str) == Some("__closure_id") => {
                Some(*value)
            }
            _ => None,
        })
        .collect()
}

// ── (a) inner-first: every outer call resolves to the named callee ──────────────────────────

#[test]
fn inner_first_outer_calls_resolve_to_the_named_callee() {
    let compilation = compile(INNER_FIRST);
    let outer = module_bytes(&compilation, Ring::Outer);
    let imports = import_count(outer);
    assert_eq!(
        misdirected_calls(outer, &compilation.air, Ring::Outer),
        Vec::new(),
        "every outer call must target the callee the AIR names"
    );
    // Name-level statement of the same fact: the exported `tool__tool_main` body calls
    // `helper`'s index and nothing else; `helper` is a different function from itself.
    let tool_main = exports(outer)
        .into_iter()
        .find(|(name, _)| name == "tool__tool_main")
        .map(|(_, index)| index)
        .expect("tool_main is exported");
    let helper = index_of(&compilation.air, Ring::Outer, imports, "tool::helper");
    assert_ne!(helper, tool_main);
    let bodies = emitted_user_calls(outer);
    assert_eq!(bodies[(tool_main - imports) as usize], vec![helper]);
    // The layout is the one the defect needs: `helper`'s GLOBAL id is not its local position.
    let global = global_id(&compilation.air, "tool::helper");
    assert_ne!(
        imports + global,
        helper,
        "inner-first layout: global id != local index"
    );
}

// ── (c) the swapped twin still works, and the outer artifact no longer depends on layout ─────

#[test]
fn outer_first_twin_resolves_and_outer_bytes_are_layout_independent() {
    let inner_first = compile(INNER_FIRST);
    let outer_first = compile(OUTER_FIRST);
    assert_eq!(
        misdirected_calls(
            module_bytes(&outer_first, Ring::Outer),
            &outer_first.air,
            Ring::Outer
        ),
        Vec::new()
    );
    // The code section (every call index) is a function of the outer ring alone. The whole
    // module is NOT byte-identical across layouts: the element segment places the ring's
    // functions at their global ids, which differ between the two layouts by design.
    assert_eq!(
        emitted_user_calls(module_bytes(&inner_first, Ring::Outer)),
        emitted_user_calls(module_bytes(&outer_first, Ring::Outer)),
    );
    for compilation in [&inner_first, &outer_first] {
        assert_eq!(
            misplaced_table_slots(
                module_bytes(compilation, Ring::Outer),
                &compilation.air,
                Ring::Outer
            ),
            Vec::new()
        );
    }
}

#[test]
fn outer_first_inner_calls_resolve_and_inner_bytes_are_layout_independent() {
    let outer_first = compile(INNER_CALLS_OUTER_FIRST);
    let inner_first = compile(INNER_CALLS_INNER_FIRST);
    for compilation in [&outer_first, &inner_first] {
        assert_eq!(
            misdirected_calls(&compilation.wasm_inner, &compilation.air, Ring::Inner),
            Vec::new()
        );
        assert_eq!(
            misplaced_table_slots(&compilation.wasm_inner, &compilation.air, Ring::Inner),
            Vec::new()
        );
    }
    assert_eq!(
        emitted_user_calls(&outer_first.wasm_inner),
        emitted_user_calls(&inner_first.wasm_inner)
    );
}

// ── the security-relevant shape: a same-signature neighbour ─────────────────────────────────

#[test]
fn same_signature_neighbour_is_not_called() {
    let compilation = compile(COLLISION);
    let outer = module_bytes(&compilation, Ring::Outer);
    let imports = import_count(outer);
    let plus_one = index_of(&compilation.air, Ring::Outer, imports, "tool::plus_one");
    let times_hundred = index_of(
        &compilation.air,
        Ring::Outer,
        imports,
        "tool::times_hundred",
    );
    let tool_main = index_of(&compilation.air, Ring::Outer, imports, "tool::tool_main");
    let bodies = emitted_user_calls(outer);
    assert_eq!(bodies[(tool_main - imports) as usize], vec![plus_one]);
    assert_ne!(plus_one, times_hundred);
    assert_eq!(
        misdirected_calls(outer, &compilation.air, Ring::Outer),
        Vec::new()
    );
}

// ── closures: the stored slot is the global id and the table places the closure there ──────

#[test]
fn closure_table_slot_is_its_global_id_and_the_ring_table_places_it_there() {
    let compilation = compile(CLOSURE);
    let air = &compilation.air;
    let partition = ring_partition(air, Ring::Outer);
    let (closure_global, closure_position) = partition
        .iter()
        .enumerate()
        .find_map(|(position, (id, f))| {
            matches!(f.kind, AirFunctionKind::Closure).then_some((id.0, position as u32))
        })
        .expect("the outer ring holds the closure");
    assert_ne!(
        closure_global, closure_position,
        "inner-first layout: the closure's global id is not its ring-local position"
    );
    // The AIR is untouched by the fix: the stored slot IS the global id.
    let tool_main = partition
        .iter()
        .find(|(_, f)| f.name == "tool::tool_main")
        .map(|(_, f)| *f)
        .expect("tool_main is in the outer ring");
    assert_eq!(
        stored_closure_ids(tool_main),
        vec![i64::from(closure_global)]
    );
    // The emitted outer table spans every global id, holds the closure's wasm index at its
    // global slot, and leaves the inner ring's slots uninitialized.
    let outer = module_bytes(&compilation, Ring::Outer);
    assert_eq!(misplaced_table_slots(outer, air, Ring::Outer), Vec::new());
    let (size, slots) = table_layout(outer);
    assert_eq!(size, air.functions.len() as u64);
    let closure_index = import_count(outer) + closure_position;
    assert!(slots.contains(&(closure_global, closure_index)));
    let inner_ids: Vec<u32> = ring_partition(air, Ring::Inner)
        .iter()
        .map(|(id, _)| id.0)
        .collect();
    assert_eq!(
        inner_ids,
        vec![0, 1],
        "two inner functions precede the outer ring"
    );
    assert!(slots.iter().all(|(slot, _)| !inner_ids.contains(slot)));
    // The inner module obeys the same rule from the other side.
    assert_eq!(
        misplaced_table_slots(&compilation.wasm_inner, air, Ring::Inner),
        Vec::new()
    );
}

#[test]
fn same_signature_closure_neighbour_is_not_in_the_named_closures_slot() {
    let compilation = compile(CLOSURE_COLLISION);
    let air = &compilation.air;
    let outer = module_bytes(&compilation, Ring::Outer);
    let imports = import_count(outer);
    let partition = ring_partition(air, Ring::Outer);
    let closures: Vec<(u32, u32)> = partition
        .iter()
        .enumerate()
        .filter(|(_, (_, f))| matches!(f.kind, AirFunctionKind::Closure))
        .map(|(position, (id, _))| (id.0, imports + position as u32))
        .collect();
    assert_eq!(closures.len(), 2, "two same-signature closures");
    let tool_main = partition
        .iter()
        .find(|(_, f)| f.name == "tool::tool_main")
        .map(|(_, f)| *f)
        .expect("tool_main is in the outer ring");
    // Both constructions store their own global id, and each slot holds its own closure.
    let stored = stored_closure_ids(tool_main);
    assert_eq!(
        stored,
        closures
            .iter()
            .map(|(id, _)| i64::from(*id))
            .collect::<Vec<_>>()
    );
    let (_, slots) = table_layout(outer);
    for (id, index) in &closures {
        assert!(slots.contains(&(*id, *index)));
    }
    assert_eq!(misplaced_table_slots(outer, air, Ring::Outer), Vec::new());
}

// ── actor handlers (inner-only) with an outer module present and first ──────────────────────

#[test]
fn actor_handler_calls_resolve_with_an_outer_module_first() {
    let compilation = compile(ACTOR);
    assert!(compilation.wasm_outer.is_some(), "the fixture is two-ring");
    assert_eq!(
        misdirected_calls(&compilation.wasm_inner, &compilation.air, Ring::Inner),
        Vec::new()
    );
    assert_eq!(
        misplaced_table_slots(&compilation.wasm_inner, &compilation.air, Ring::Inner),
        Vec::new()
    );
}

// ── a cross-ring call reaching emission is an ICE, never a plausible index ──────────────────

/// `INNER_FIRST`'s AIR with `tool::tool_main`'s single direct call redirected at the inner
/// `first::dummy`. No source produces this shape (R004 rejects a cross-ring call, and R007
/// rejects the lowered one), so it is hand-built: the ICE below is the emitter's BACKSTOP for
/// the gate, and this is the only way to reach it.
fn cross_ring_air() -> AirProgram {
    let mut air = compile(INNER_FIRST).air;
    let dummy = FuncId(global_id(&air, "first::dummy"));
    let tool_main = air
        .functions
        .iter_mut()
        .find(|f| f.name == "tool::tool_main")
        .expect("tool_main is lowered");
    let mut rewritten = 0;
    for stmt in tool_main.blocks.iter_mut().flat_map(|b| b.stmts.iter_mut()) {
        if let AirStmt::Call { func, .. } = stmt {
            *func = dummy;
            rewritten += 1;
        }
    }
    assert_eq!(
        rewritten, 1,
        "the fixture has exactly one direct call to redirect"
    );
    air
}

#[test]
fn cross_ring_call_reaching_emission_is_an_ice() {
    let air = cross_ring_air();
    let outcome = catch_unwind(AssertUnwindSafe(|| wasm::emit(&air)));
    let payload = outcome
        .err()
        .expect("emission must refuse the cross-ring call");
    let message = payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| (*s).to_owned()))
        .expect("panic payload is a message");
    assert!(
        message.starts_with("ICE:") && message.contains("crossing the ring boundary"),
        "expected a narrated ring-boundary ICE, got: {message}"
    );
}

// ── ROUND 2: the source-level generic shape, in both layouts ─────────────────────

/// Exactly the error codes `compile_module` reports for `src`, sorted and deduplicated.
/// EXACT SET, never a substring of the rendered output.
fn error_codes(src: &str) -> BTreeSet<String> {
    match compile_module(src) {
        Ok(_) => BTreeSet::new(),
        Err(err) => err
            .diagnostics()
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect(),
    }
}

/// The defect round 1 missed: the existing cross-ring test hand-rewrote an AIR `Call`, so the
/// only shape it covered was one no source could produce. These two programs are SOURCE, they
/// pass every source-level checker (R004 included: both calls are same-module), and `main`
/// compiles them into a misdirected artifact. The gate must reject them with R007 in BOTH
/// layouts — the inner-first one and its outer-first mirror.
#[test]
fn a_generic_across_the_ring_boundary_is_rejected_in_both_layouts() {
    for (label, src) in [
        ("inner module first", GENERIC_INNER_FIRST),
        ("outer module first (mirror)", GENERIC_OUTER_FIRST_MIRROR),
    ] {
        assert_eq!(
            error_codes(src),
            BTreeSet::from(["R007".to_string()]),
            "{label}: a generic filed in the other ring must be exactly R007"
        );
    }
}

/// The diagnostic must be reachable through the ordinary pipeline, not only through the
/// standalone gate: `compile_module` must RETURN it rather than panic. A panic would be caught
/// by the harness as a test failure anyway, but this states the property the reviewer's
/// finding was about — `check`/`forge` on a program `main` compiles must not ICE.
#[test]
fn the_generic_shape_returns_a_diagnostic_instead_of_panicking() {
    for src in [GENERIC_INNER_FIRST, GENERIC_OUTER_FIRST_MIRROR] {
        let outcome = catch_unwind(AssertUnwindSafe(|| compile_module(src)));
        let result = outcome.expect("compilation must not panic on a legal source program");
        let err = result.expect_err("the gate rejects this program");
        assert_eq!(err.diagnostics().len(), 1, "one call, one diagnostic");
        let diagnostic = &err.diagnostics()[0];
        assert_eq!(diagnostic.code().as_str(), "R007");
        assert!(
            diagnostic.span().is_some(),
            "R007 must anchor in source, not float"
        );
    }
}

/// ANTI-STUB (SC-P4) for the absence claim "no cross-ring call reaches emission": the gate is
/// only evidence if it is silent on the programs that are fine. The definer-first control is
/// the same source with the modules reordered — it must compile, emit BOTH modules, and place
/// the instance in the caller's ring; every other two-ring fixture in this file must stay
/// clean too, so the gate cannot be passing by rejecting everything.
#[test]
fn the_gate_is_silent_on_two_ring_programs_that_are_placed_correctly() {
    let compilation = compile(GENERIC_DEFINER_FIRST);
    assert!(
        compilation.wasm_outer.is_some(),
        "the control is a two-ring program"
    );
    let caller_ring = compilation
        .air
        .functions
        .iter()
        .find(|f| f.name == "tool::tool_main")
        .expect("tool_main is lowered")
        .ring;
    let instance = compilation
        .air
        .functions
        .iter()
        .find(|f| f.name.starts_with("tool::ident"))
        .expect("the monomorphized instance is lowered");
    assert_eq!(
        instance.ring, caller_ring,
        "definer-first puts the instance in the caller's ring"
    );

    for (label, src) in [
        ("INNER_FIRST", INNER_FIRST),
        ("OUTER_FIRST", OUTER_FIRST),
        ("INNER_CALLS_OUTER_FIRST", INNER_CALLS_OUTER_FIRST),
        ("INNER_CALLS_INNER_FIRST", INNER_CALLS_INNER_FIRST),
        ("COLLISION", COLLISION),
        ("GENERIC_DEFINER_FIRST", GENERIC_DEFINER_FIRST),
    ] {
        assert_eq!(
            error_codes(src),
            BTreeSet::new(),
            "{label}: the gate must not reject a correctly placed two-ring program"
        );
    }
}

/// The gate itself, applied to the hand-built AIR the emitter would ICE on: it must produce
/// R007 rather than leave the ICE as the only defense. This is the unit the pipeline calls.
#[test]
fn the_gate_rejects_the_hand_built_cross_ring_air() {
    let air = cross_ring_air();
    let diagnostics = ring_check::check_air_ring_placement(&air)
        .expect_err("a cross-ring call in AIR must be rejected");
    assert_eq!(
        diagnostics
            .iter()
            .map(|d| d.code().as_str().to_string())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from(["R007".to_string()])
    );
    // ANTI-STUB: the same checker must accept the unmodified program, or "it rejected the
    // planted call" proves nothing.
    let clean = compile(INNER_FIRST).air;
    assert!(
        ring_check::check_air_ring_placement(&clean).is_ok(),
        "the gate must accept the fixture it was derived from"
    );
}

// ── SC-P4 anti-stubs: the old formulas' bytes are detected ──────────────────────────────────

/// Patch the single-byte immediate of the `call` in the defined function `target` from
/// `from` to `to`, located by operator offset (not by byte search).
fn patch_call_immediate(bytes: &[u8], imports: u32, target: u32, from: u32, to: u32) -> Vec<u8> {
    assert!(from < 0x80 && to < 0x80, "single-byte LEB immediates");
    let mut patched = bytes.to_vec();
    let mut defined = 0u32;
    let mut sites = 0;
    for payload in Parser::new(0).parse_all(bytes) {
        if let Payload::CodeSectionEntry(body) = payload.expect("valid wasm") {
            if imports + defined == target {
                let mut reader = body.get_operators_reader().expect("valid body");
                while !reader.eof() {
                    let (op, offset) = reader.read_with_offset().expect("valid operator");
                    if let Operator::Call { function_index } = op
                        && function_index == from
                    {
                        assert_eq!(bytes[offset], 0x10, "`call` opcode at the operator offset");
                        assert_eq!(bytes[offset + 1], from as u8);
                        patched[offset + 1] = to as u8;
                        sites += 1;
                    }
                }
            }
            defined += 1;
        }
    }
    assert_eq!(sites, 1, "exactly one call site patched");
    patched
}

#[test]
fn anti_stub_old_formula_index_is_detected_although_it_validates() {
    let compilation = compile(COLLISION);
    let outer = module_bytes(&compilation, Ring::Outer);
    let imports = import_count(outer);
    let plus_one = index_of(&compilation.air, Ring::Outer, imports, "tool::plus_one");
    let tool_main = index_of(&compilation.air, Ring::Outer, imports, "tool::tool_main");
    // The pre-fix formula: `import_count + global FuncId`.
    let old_index = imports + global_id(&compilation.air, "tool::plus_one");
    assert_ne!(
        old_index, plus_one,
        "the layout makes the old formula wrong"
    );
    let planted = patch_call_immediate(outer, imports, tool_main, plus_one, old_index);
    assert_ne!(planted, outer);
    // The validator is NOT a detector: the misdirected call has a matching signature.
    wasmparser::validate(&planted).expect("the misdirected module validates");
    let times_hundred = index_of(
        &compilation.air,
        Ring::Outer,
        imports,
        "tool::times_hundred",
    );
    assert_eq!(
        old_index, times_hundred,
        "the old formula lands on the same-signature neighbour"
    );
    // This checker IS a detector.
    assert_eq!(
        misdirected_calls(&planted, &compilation.air, Ring::Outer),
        vec![(
            "tool::tool_main".to_owned(),
            vec![old_index],
            vec![plus_one]
        )]
    );
}

/// Rewrite the fixed module's table back to the pre-fix COMPACT layout: `ring_count` slots,
/// one segment at offset 0 holding the ring's functions in order. Both patches are located by
/// section/segment range and assert the exact byte shapes they overwrite.
fn plant_compact_table(
    bytes: &[u8],
    table_size: u32,
    ring_count: u32,
    segment_offset: u32,
) -> Vec<u8> {
    assert!(table_size < 0x80 && ring_count < 0x80 && segment_offset < 0x40);
    let mut patched = bytes.to_vec();
    let mut tables = 0;
    let mut segments = 0;
    for payload in Parser::new(0).parse_all(bytes) {
        match payload.expect("valid wasm") {
            Payload::TableSection(section) => {
                // count=1, funcref, limits flag 0x01 (min+max), min, max
                let at = section.range().start;
                assert_eq!(&bytes[at..at + 3], &[0x01, 0x70, 0x01]);
                assert_eq!(
                    &bytes[at + 3..at + 5],
                    &[table_size as u8, table_size as u8]
                );
                patched[at + 3] = ring_count as u8;
                patched[at + 4] = ring_count as u8;
                tables += 1;
            }
            Payload::ElementSection(section) => {
                for element in section {
                    let element = element.expect("valid element");
                    // active segment with an explicit table index: flags 0x02, table 0,
                    // `i32.const <offset>`, `end`
                    let at = element.range.start;
                    assert_eq!(&bytes[at..at + 3], &[0x02, 0x00, 0x41]);
                    assert_eq!(bytes[at + 3], segment_offset as u8);
                    assert_eq!(bytes[at + 4], 0x0B);
                    patched[at + 3] = 0;
                    segments += 1;
                }
            }
            _ => {}
        }
    }
    assert_eq!(
        (tables, segments),
        (1, 1),
        "one table, one segment to rewrite"
    );
    patched
}

#[test]
fn anti_stub_old_compact_table_is_detected_although_it_validates() {
    let compilation = compile(CLOSURE_COLLISION);
    let air = &compilation.air;
    let outer = module_bytes(&compilation, Ring::Outer);
    let imports = import_count(outer);
    let partition = ring_partition(air, Ring::Outer);
    let first_outer_id = partition[0].0.0;
    assert_eq!(
        first_outer_id, 1,
        "one inner function precedes the outer ring"
    );
    let planted = plant_compact_table(
        outer,
        air.functions.len() as u32,
        partition.len() as u32,
        first_outer_id,
    );
    assert_ne!(planted, outer);
    // The validator is NOT a detector: a compact table is a well-formed table.
    wasmparser::validate(&planted).expect("the compact-table module validates");
    // In the compact table, closure `a`'s stored id (2) is the slot of closure `b`, a
    // same-signature function: `call_indirect` would dispatch to it, not trap.
    let closures: Vec<(u32, u32)> = partition
        .iter()
        .enumerate()
        .filter(|(_, (_, f))| matches!(f.kind, AirFunctionKind::Closure))
        .map(|(position, (id, _))| (id.0, imports + position as u32))
        .collect();
    let [(a, _), (b, b_index)] = closures[..] else {
        panic!("two lifted closures in the outer ring, got {closures:?}");
    };
    assert_eq!((a, b), (2, 3), "the fixture's documented global ids");
    let (_, planted_slots) = table_layout(&planted);
    assert!(planted_slots.contains(&(a, b_index)));
    // This checker IS a detector: the table is short, `a` and `b` are not at their own slots,
    // and slot 0 (an inner id) is initialized.
    let report = misplaced_table_slots(&planted, air, Ring::Outer);
    assert!(report.iter().any(|(name, ..)| name == "<table size>"));
    assert!(
        report
            .iter()
            .any(|(_, slot, actual, _)| *slot == a && *actual == Some(b_index))
    );
    assert!(report.iter().any(|(_, slot, ..)| *slot == b));
    assert!(
        report
            .iter()
            .any(|(name, slot, ..)| name == "<foreign slot>" && *slot == 0)
    );
}
