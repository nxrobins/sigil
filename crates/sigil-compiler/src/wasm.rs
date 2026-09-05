//! The Wasm backend: `emit` encodes a verified, memory- and fuel-lowered
//! `AirProgram` into module bytes with `wasm_encoder`. Two-ring programs
//! split into an inner module (the full eight-import runtime set) and an
//! outer module (reduced set: fuel_decrement and alloc only).
//!
//! This file owns the emitted ABI byte for byte: the fixed runtime-import
//! prefix in pinned index order; local function index = import count plus
//! position in the function vector; ffi imports, then the conditional
//! `alloc_persistent`, appended AFTER the fixed prefix so a state-free
//! module is byte-unchanged (AGG2b-2); string literals deduplicated by
//! content and packed from offset 1024, with the bump pointer starting at
//! the 8-aligned end of static data. The self-hosted emitter
//! (`selfhost/air.sigil`) must reproduce these bytes exactly on its
//! supported surface (unsupported forms poison, never diverge), so ANY
//! encoding change is a contract change against `docs/specs/sh-wasm.md`.
//! The `ct_eq`/`ct_select`/`ct_lt` sequences are additionally a
//! constant-time surface: branch-free by construction, opcode-audited per
//! `docs/specs/secret-ct.md`.
//!
//! Emission is total and emits no diagnostics; a malformed input (an import
//! missing from the active set, an unsupported op/type pairing) is an
//! `ICE:`-prefixed panic, never plausible wrong bytes. Pinned by
//! `sigil-runtime/tests/air_differential.rs` (byte-exact differential),
//! `tests/determinism_lock.rs` (run-over-run byte equality), and
//! `tests/taint_ct_audit.rs` (the constant-time opcode audit).

use std::collections::{BTreeMap, HashSet};

use sigil_abi::host_contract::{HOST_PROFILE_SECTION, HostProfileRequirement};

pub use sigil_abi::{
    RUNTIME_IMPORT_ALLOC, RUNTIME_IMPORT_ALLOC_PERSISTENT, RUNTIME_IMPORT_ASK,
    RUNTIME_IMPORT_CAP_MINT, RUNTIME_IMPORT_CAP_RESTRICT, RUNTIME_IMPORT_CAP_SPLIT,
    RUNTIME_IMPORT_FUEL_DECREMENT, RUNTIME_IMPORT_MODULE, RUNTIME_IMPORT_SEND,
    RUNTIME_IMPORT_SPAWN,
};
use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, ElementSection, Elements, EntityType,
    ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType, ImportSection,
    Instruction, MemArg, MemorySection, MemoryType, Module, RefType, TableSection, TableType,
    TypeSection, ValType,
};

use crate::air::{
    AirBlock, AirFunction, AirFunctionKind, AirProgram, AirStmt, AirSupervisionStrategy,
    AirTerminator, AirType, AirValue, BlockId, HandlerId, VarId,
};
use crate::ast::{BinaryOp, Ring};

/// Lookup-only codegen state. Keeping these maps ordered makes accidental
/// future iteration deterministic without obscuring their intended use.
type LookupMap<K, V> = BTreeMap<K, V>;

/// Output of Wasm code generation. Two-ring programs produce separate inner
/// and outer modules; single-ring programs set `outer` to `None`.
pub struct WasmOutput {
    pub inner: Vec<u8>,
    pub outer: Option<Vec<u8>>,
}

const FUEL_DECREMENT_IMPORT_INDEX: u32 = 0;
const SEND_IMPORT_INDEX: u32 = 1;
const ASK_IMPORT_INDEX: u32 = 2;
const SPAWN_IMPORT_INDEX: u32 = 3;
const ALLOC_IMPORT_INDEX: u32 = 4;
const CAP_RESTRICT_IMPORT_INDEX: u32 = 5;
const CAP_SPLIT_IMPORT_INDEX: u32 = 6;
const CAP_MINT_IMPORT_INDEX: u32 = 7;
const IMPORT_COUNT: u32 = 8;
const STATIC_DATA_BASE: u32 = 1024;

pub fn emit(program: &AirProgram) -> WasmOutput {
    let has_outer = program.functions.iter().any(|f| f.ring == Ring::Outer);

    if !has_outer {
        // Single-ring: emit all functions into inner (backward-compatible path).
        let inner = emit_module(&program.functions, ImportSet::Full);
        return WasmOutput { inner, outer: None };
    }

    // Two-ring: partition by ring annotation.
    let inner_fns: Vec<&AirFunction> = program
        .functions
        .iter()
        .filter(|f| f.ring == Ring::Inner)
        .collect();
    let outer_fns: Vec<&AirFunction> = program
        .functions
        .iter()
        .filter(|f| f.ring == Ring::Outer)
        .collect();

    let inner = emit_module_refs(&inner_fns, ImportSet::Full);
    let outer = emit_module_refs(&outer_fns, ImportSet::Reduced);

    WasmOutput {
        inner,
        outer: Some(outer),
    }
}

/// Bind an occurrence-aware compilation to the exact host declaration profile
/// that the verifier checked. Every emitted ring carries the same requirement:
/// a runtime may instantiate either artifact independently, so putting the
/// assumption on only the selected/tool ring would leave the other artifact
/// unbound.
///
/// The payload encoding belongs to `sigil-abi`; this function only performs
/// canonical Wasm custom-section framing. Call it at most once per output.
pub(crate) fn append_host_profile_requirement(
    output: &mut WasmOutput,
    requirement: HostProfileRequirement,
) {
    let payload = requirement.encode();
    append_custom_section(&mut output.inner, HOST_PROFILE_SECTION, &payload);
    if let Some(outer) = &mut output.outer {
        append_custom_section(outer, HOST_PROFILE_SECTION, &payload);
    }
}

fn append_custom_section(wasm: &mut Vec<u8>, name: &str, payload: &[u8]) {
    let mut content = Vec::with_capacity(uleb_len(name.len()) + name.len() + payload.len());
    append_uleb(&mut content, name.len());
    content.extend_from_slice(name.as_bytes());
    content.extend_from_slice(payload);

    // Section id 0 denotes a custom section. Appending a section after the
    // existing module is valid Wasm and does not perturb function indices or
    // runtime code generation.
    wasm.push(0);
    append_uleb(wasm, content.len());
    wasm.extend_from_slice(&content);
}

fn append_uleb(bytes: &mut Vec<u8>, mut value: usize) {
    loop {
        let low = (value & 0x7f) as u8;
        value >>= 7;
        bytes.push(low | if value == 0 { 0 } else { 0x80 });
        if value == 0 {
            return;
        }
    }
}

fn uleb_len(mut value: usize) -> usize {
    let mut length = 1;
    while value >= 0x80 {
        value >>= 7;
        length += 1;
    }
    length
}

/// Which set of runtime imports to include in the emitted module.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ImportSet {
    /// All 7 imports (fuel_decrement, send, ask, spawn, alloc, cap_restrict,
    /// cap_split). The historical `fuel_exhausted` import was removed in
    /// step 15 of the supremum loop — it was declared by every Sigil
    /// module but never called from emitted WASM. Exhaustion is signalled by
    /// the HOST: `fuel_decrement` refuses an overrunning decrement and traps,
    /// on both runtime paths (actor: runtime.rs:586-588; ephemeral/forge:
    /// ephemeral.rs `link_sigil_imports`). The emitted `(i32) -> ()` import
    /// type carries no status back to the guest and needs none — a trap
    /// unwinds it without its cooperation.
    Full,
    /// Reduced set for outer ring: fuel_decrement, alloc only.
    Reduced,
}

/// Outer-ring import indices (reduced set).
const OUTER_FUEL_DECREMENT_IMPORT_INDEX: u32 = 0;
const OUTER_ALLOC_IMPORT_INDEX: u32 = 1;
const OUTER_IMPORT_COUNT: u32 = 2;

#[derive(Clone, Copy)]
struct BuiltinImportIndices {
    fuel_decrement: u32,
    send: Option<u32>,
    ask: Option<u32>,
    spawn: Option<u32>,
    alloc: u32,
    cap_restrict: Option<u32>,
    cap_split: Option<u32>,
    cap_mint: Option<u32>,
    /// AGG2b-2: the persistent-heap alloc channel (`alloc_persistent`). `None` unless the module
    /// contains a `persistent` IntrinsicAlloc (a state-backed `Vec<scalar>` instance); then it is a
    /// CONDITIONAL-APPEND import, resolved to `base_import_count + ffi.len()` in `emit_module_refs`
    /// AFTER the ffi imports — never in the fixed prefix (P2), so a state-free module is unchanged.
    alloc_persistent: Option<u32>,
}

#[derive(Debug, Clone)]
struct FfiImport {
    key: String,
    name: String,
    params: Vec<ValType>,
    results: Vec<ValType>,
    type_index: u32,
    func_index: u32,
}

#[derive(Debug, Clone)]
struct StaticDataSegment {
    offset: u32,
    bytes: Vec<u8>,
}

#[derive(Debug, Clone)]
struct StaticDataLayout {
    offsets: LookupMap<String, u32>,
    segments: Vec<StaticDataSegment>,
    bump_ptr_start: u32,
}

fn base_import_count(import_set: ImportSet) -> u32 {
    match import_set {
        ImportSet::Full => IMPORT_COUNT,
        ImportSet::Reduced => OUTER_IMPORT_COUNT,
    }
}

fn builtin_import_indices(import_set: ImportSet) -> BuiltinImportIndices {
    match import_set {
        ImportSet::Full => BuiltinImportIndices {
            fuel_decrement: FUEL_DECREMENT_IMPORT_INDEX,
            send: Some(SEND_IMPORT_INDEX),
            ask: Some(ASK_IMPORT_INDEX),
            spawn: Some(SPAWN_IMPORT_INDEX),
            alloc: ALLOC_IMPORT_INDEX,
            cap_restrict: Some(CAP_RESTRICT_IMPORT_INDEX),
            cap_split: Some(CAP_SPLIT_IMPORT_INDEX),
            cap_mint: Some(CAP_MINT_IMPORT_INDEX),
            // Resolved dynamically in emit_module_refs iff a persistent alloc exists (P2).
            alloc_persistent: None,
        },
        ImportSet::Reduced => BuiltinImportIndices {
            fuel_decrement: OUTER_FUEL_DECREMENT_IMPORT_INDEX,
            send: None,
            ask: None,
            spawn: None,
            alloc: OUTER_ALLOC_IMPORT_INDEX,
            cap_restrict: None,
            cap_split: None,
            cap_mint: None,
            alloc_persistent: None,
        },
    }
}

fn ffi_signature(
    function: &AirFunction,
    dst: &Option<VarId>,
    args: &[VarId],
) -> (Vec<ValType>, Vec<ValType>) {
    let params = args
        .iter()
        .map(|arg| wasm_type(function.var_type(*arg)))
        .collect::<Vec<_>>();
    let results = dst
        .map(|var| vec![wasm_type(function.var_type(var))])
        .unwrap_or_default();
    (params, results)
}

fn ffi_import_key(name: &str, params: &[ValType], results: &[ValType]) -> String {
    format!("{name}|{params:?}|{results:?}")
}

/// AGG2b-2: does any function contain a `persistent` IntrinsicAlloc (a state-backed `Vec<scalar>`
/// instance's grow-alloc)? If so, `alloc_persistent` is conditionally appended as the import right
/// after the ffi imports; if not (every stateless module, incl. the self-host capstone), nothing is
/// appended and `import_count` is unchanged — byte-identical.
fn module_has_persistent_alloc(functions: &[&AirFunction]) -> bool {
    functions.iter().any(|function| {
        function.blocks.iter().any(|block| {
            block.stmts.iter().any(|stmt| {
                matches!(
                    stmt,
                    AirStmt::IntrinsicAlloc {
                        persistent: true,
                        ..
                    } | AirStmt::BumpAlloc {
                        persistent: true,
                        ..
                    } | AirStmt::PromoteBytes { .. }
                )
            })
        })
    })
}

fn collect_ffi_imports(functions: &[&AirFunction], base_import_count: u32) -> Vec<FfiImport> {
    let mut imports = Vec::new();
    let mut seen = HashSet::new();

    for function in functions {
        for block in &function.blocks {
            for stmt in &block.stmts {
                let AirStmt::ExternCall {
                    dst,
                    extern_name,
                    args,
                } = stmt
                else {
                    continue;
                };

                let (params, results) = ffi_signature(function, dst, args);
                let key = ffi_import_key(extern_name, &params, &results);
                if !seen.insert(key.clone()) {
                    continue;
                }

                let index = imports.len() as u32;
                imports.push(FfiImport {
                    key,
                    name: extern_name.clone(),
                    params,
                    results,
                    type_index: base_import_count + index,
                    func_index: base_import_count + index,
                });
            }
        }
    }

    imports
}

fn align_up(value: u32, align: u32) -> u32 {
    if align <= 1 {
        return value;
    }
    value.div_ceil(align) * align
}

fn collect_static_data(functions: &[&AirFunction]) -> StaticDataLayout {
    let mut offsets = LookupMap::new();
    let mut segments = Vec::new();
    let mut cursor = STATIC_DATA_BASE;

    for function in functions {
        for block in &function.blocks {
            for stmt in &block.stmts {
                let AirStmt::Assign {
                    val: AirValue::StrLit(value),
                    ..
                } = stmt
                else {
                    continue;
                };

                if offsets.contains_key(value) {
                    continue;
                }

                let bytes = value.as_bytes().to_vec();
                offsets.insert(value.clone(), cursor);
                segments.push(StaticDataSegment {
                    offset: cursor,
                    bytes: bytes.clone(),
                });
                cursor += bytes.len() as u32;
            }
        }
    }

    StaticDataLayout {
        offsets,
        segments,
        bump_ptr_start: align_up(cursor, 8),
    }
}

/// Emit a wasm module from a slice of owned `AirFunction`s.
fn emit_module(functions: &[AirFunction], import_set: ImportSet) -> Vec<u8> {
    let refs: Vec<&AirFunction> = functions.iter().collect();
    emit_module_refs(&refs, import_set)
}

/// Emit a wasm module from a slice of borrowed `AirFunction`s.
fn emit_module_refs(functions: &[&AirFunction], import_set: ImportSet) -> Vec<u8> {
    let mut builtins = builtin_import_indices(import_set);
    let base_import_count = base_import_count(import_set);
    let ffi_imports = collect_ffi_imports(functions, base_import_count);
    let ffi_import_map = ffi_imports
        .iter()
        .map(|import| (import.key.clone(), import.func_index))
        .collect::<LookupMap<_, _>>();
    // AGG2b-2: `alloc_persistent` is a CONDITIONAL-APPEND import — present iff a state-backed
    // `Vec<scalar>` instance emitted a persistent alloc. It goes at the index right after the ffi
    // imports (a new type AND a new import, both after the ffi ones), so a stateless module's
    // `import_count` is unchanged and byte-identical (P2). A state-backed module's function indices
    // shift by 1 uniformly and self-consistently (`import_count` threads through every index).
    let has_persistent_alloc = module_has_persistent_alloc(functions);
    if has_persistent_alloc {
        builtins.alloc_persistent = Some(base_import_count + ffi_imports.len() as u32);
    }
    let import_count =
        base_import_count + ffi_imports.len() as u32 + u32::from(has_persistent_alloc);
    let static_data = collect_static_data(functions);

    let mut module = Module::new();

    let mut types = TypeSection::new();
    // Type indices 0..N are for the import signatures.
    match import_set {
        ImportSet::Full => {
            // 0: fuel_decrement (i32) -> ()
            types.ty().function([ValType::I32], []);
            // 1: send (i32,i32,i32,i32) -> ()
            types
                .ty()
                .function([ValType::I32, ValType::I32, ValType::I32, ValType::I32], []);
            // 2: ask (i32,i32,i32,i32,i64) -> i64
            types.ty().function(
                [
                    ValType::I32,
                    ValType::I32,
                    ValType::I32,
                    ValType::I32,
                    ValType::I64,
                ],
                [ValType::I64],
            );
            // 3: spawn (i32,i32,i32,i32,i32) -> i32
            types.ty().function(
                [
                    ValType::I32,
                    ValType::I32,
                    ValType::I32,
                    ValType::I32,
                    ValType::I32,
                ],
                [ValType::I32],
            );
            // 4: alloc (i32) -> i32
            types.ty().function([ValType::I32], [ValType::I32]);
            // 5: cap_restrict (i32,i32) -> i32
            types
                .ty()
                .function([ValType::I32, ValType::I32], [ValType::I32]);
            // 6: cap_split (i32,i64) -> i32
            types
                .ty()
                .function([ValType::I32, ValType::I64], [ValType::I32]);
            // 7: cap_mint () -> i32
            types.ty().function([], [ValType::I32]);
        }
        ImportSet::Reduced => {
            // 0: fuel_decrement (i32) -> ()
            types.ty().function([ValType::I32], []);
            // 1: alloc (i32) -> i32
            types.ty().function([ValType::I32], [ValType::I32]);
        }
    }
    for ffi_import in &ffi_imports {
        types
            .ty()
            .function(ffi_import.params.clone(), ffi_import.results.clone());
    }
    // AGG2b-2: alloc_persistent's signature `(i32) -> i32` (same as alloc), appended after the ffi
    // types iff present, at type index `base_import_count + ffi.len()` — the index its import
    // references below. Absent from stateless modules (byte-identical type section).
    if has_persistent_alloc {
        types.ty().function([ValType::I32], [ValType::I32]);
    }

    // `type_map` is used ONLY for `call_indirect` type-index lookup.
    let mut type_map: LookupMap<(Vec<ValType>, Vec<ValType>), u32> = LookupMap::new();

    // The type section gets ONE entry per function, at a sequential index
    // (`import_count + position`) — exactly what the FunctionSection below
    // assigns each function. `type_map` must stay in lockstep with that
    // sequential layout: record each signature's index, OVERWRITING any prior
    // entry. A prior `or_insert` deduped — leaving the running index
    // un-advanced on a repeated signature while the section still grew — so
    // every later `type_map` index pointed one (or more) slots before its real
    // type entry. A bool-returning (or 2-arg) closure's `call_indirect` then
    // resolved to a wrong-result type → wasm "type mismatch: expected i32,
    // found i64". Overwriting is sound because duplicate signatures are
    // identical, so any of their indices is a valid `call_indirect` target.
    for (i, function) in functions.iter().enumerate() {
        let params: Vec<ValType> = function
            .params
            .iter()
            .map(|(_, ty)| wasm_type(*ty))
            .collect();
        let results: Vec<ValType> = match function.ret {
            AirType::Unit => Vec::new(),
            ty => vec![wasm_type(ty)],
        };
        type_map.insert((params.clone(), results.clone()), import_count + i as u32);
        types.ty().function(params, results);
    }
    module.section(&types);

    let mut imports = ImportSection::new();
    match import_set {
        ImportSet::Full => {
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_FUEL_DECREMENT,
                EntityType::Function(FUEL_DECREMENT_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_SEND,
                EntityType::Function(SEND_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_ASK,
                EntityType::Function(ASK_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_SPAWN,
                EntityType::Function(SPAWN_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_ALLOC,
                EntityType::Function(ALLOC_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_CAP_RESTRICT,
                EntityType::Function(CAP_RESTRICT_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_CAP_SPLIT,
                EntityType::Function(CAP_SPLIT_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_CAP_MINT,
                EntityType::Function(CAP_MINT_IMPORT_INDEX),
            );
        }
        ImportSet::Reduced => {
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_FUEL_DECREMENT,
                EntityType::Function(OUTER_FUEL_DECREMENT_IMPORT_INDEX),
            );
            imports.import(
                RUNTIME_IMPORT_MODULE,
                RUNTIME_IMPORT_ALLOC,
                EntityType::Function(OUTER_ALLOC_IMPORT_INDEX),
            );
        }
    }
    for ffi_import in &ffi_imports {
        imports.import(
            "ffi",
            &ffi_import.name,
            EntityType::Function(ffi_import.type_index),
        );
    }
    // AGG2b-2: the conditional-append `alloc_persistent` import, AFTER the ffi imports (its func
    // index == its type index == `base_import_count + ffi.len()`). Absent from stateless modules.
    if let Some(type_index) = builtins.alloc_persistent {
        imports.import(
            RUNTIME_IMPORT_MODULE,
            RUNTIME_IMPORT_ALLOC_PERSISTENT,
            EntityType::Function(type_index),
        );
    }
    module.section(&imports);

    let mut func_section = FunctionSection::new();
    for (index, _) in functions.iter().enumerate() {
        func_section.function(import_count + index as u32);
    }
    module.section(&func_section);

    // Table section must come before Memory in Wasm section order
    let func_count = functions.len() as u32;
    if func_count > 0 {
        let mut tables = TableSection::new();
        tables.table(TableType {
            element_type: RefType::FUNCREF,
            minimum: func_count as u64,
            maximum: Some(func_count as u64),
            table64: false,
            shared: false,
        });
        module.section(&tables);
    }

    let mut memories = MemorySection::new();
    memories.memory(MemoryType {
        minimum: 1,
        maximum: None,
        memory64: false,
        shared: false,
        page_size_log2: None,
    });
    module.section(&memories);

    // Global section: BUMP_PTR — mutable i32 initialized after any static data.
    let mut globals = GlobalSection::new();
    globals.global(
        GlobalType {
            val_type: ValType::I32,
            mutable: true,
            shared: false,
        },
        &ConstExpr::i32_const(static_data.bump_ptr_start as i32),
    );
    module.section(&globals);

    let mut exports = ExportSection::new();
    exports.export("memory", ExportKind::Memory, 0);
    exports.export("BUMP_PTR", ExportKind::Global, 0);
    for (index, function) in functions.iter().enumerate() {
        // Don't export internal functions. Closures are internal by kind. A `$`-prefixed
        // export name marks a synthesized internal whose ABI may differ from any original
        // declaration — e.g. an effect-desugar-rewritten abortive chain function, whose
        // declared `(..) -> T` was rewritten to `(.., $ev) -> $EhResult`. `$` is outside
        // the identifier grammar, so it never occurs in a user function's export name.
        if matches!(function.kind, AirFunctionKind::Closure)
            || function.export_name.starts_with('$')
            || !function.security.externally_callable
        {
            continue;
        }
        exports.export(
            &function.export_name,
            ExportKind::Func,
            import_count + index as u32,
        );
    }
    module.section(&exports);

    // Element section: populate function table for call_indirect
    if func_count > 0 {
        let mut elements = ElementSection::new();
        let all_indices: Vec<u32> = (0..func_count).map(|i| import_count + i).collect();
        elements.active(
            Some(0),
            &ConstExpr::i32_const(0),
            Elements::Functions(all_indices.into()),
        );
        module.section(&elements);
    }

    let mut code = CodeSection::new();
    for function in functions {
        let local_decls = function
            .locals
            .iter()
            .map(|(_, ty)| (1, wasm_type(*ty)))
            .collect::<Vec<_>>();
        let mut body = Function::new(local_decls);
        emit_function(
            function,
            &mut body,
            &type_map,
            import_count,
            builtins,
            &ffi_import_map,
            &static_data.offsets,
        );
        body.instruction(&Instruction::End);
        code.function(&body);
    }
    module.section(&code);

    if !static_data.segments.is_empty() {
        let mut data = DataSection::new();
        for segment in &static_data.segments {
            data.active(
                0,
                &ConstExpr::i32_const(segment.offset as i32),
                segment.bytes.iter().copied(),
            );
        }
        module.section(&data);
    }

    module.finish()
}

fn emit_function(
    function: &AirFunction,
    body: &mut Function,
    type_map: &LookupMap<(Vec<ValType>, Vec<ValType>), u32>,
    import_count: u32,
    builtins: BuiltinImportIndices,
    ffi_imports: &LookupMap<String, u32>,
    static_data_offsets: &LookupMap<String, u32>,
) {
    let block_map = function
        .blocks
        .iter()
        .map(|block| (block.id, block))
        .collect::<LookupMap<_, _>>();
    let mut emitted = HashSet::new();
    emit_block(
        function.entry_block,
        None,
        None,
        None,
        function,
        &block_map,
        &mut emitted,
        body,
        type_map,
        import_count,
        builtins,
        ffi_imports,
        static_data_offsets,
    );
}

/// Target the wasm emitter uses to lower an AIR `Jump(loop_header)` into the
/// correct wasm `Br N`. The `BlockId` identifies which AIR loop we want to
/// continue; the `u32` is the wasm-block depth from the current emission
/// point to that loop's `loop` label.
///
/// Why this is a struct and not just a `BlockId`: a wasm `br` instruction
/// targets blocks by structural depth, not by name. When we emit a `loop`,
/// its label sits at depth 0 from the immediate body. As we open further
/// `block`/`loop`/`if` instructions while recursing into nested AIR blocks,
/// the depth between the new emission point and the original loop label
/// grows by one for each new structured-control instruction we open.
///
/// Historical note: this used to be `Option<BlockId>` and the emitter
/// unconditionally emitted `Br(0)` when the AIR Jump target equalled the
/// remembered loop header. That works only when the Jump sits at the top of
/// the loop body — inside any nested `if`, depth 0 points at the `if` label
/// (which exits the if), not the loop label. The result was that any
/// `while { if cond { i = i + 1; } }` pattern terminated after a single
/// iteration. Surfaced while writing `stdlib/sigil/json::parse_field` in
/// Phase 5a-4; tracked in `tests/fixtures/wasm_loop_continue_in_if.sigil`.
#[derive(Copy, Clone)]
struct LoopTarget {
    /// The loop header block — a `Jump` here is a `continue` (`Br depth`, re-entering
    /// the wasm `loop`).
    header: BlockId,
    /// The loop exit block — a `Jump` here is a `break` (`Br depth+1`, leaving the
    /// `block` that wraps the loop). Only reached via an explicit `break`.
    exit: BlockId,
    depth: u32,
}

impl LoopTarget {
    /// Increment the depth — used when the emitter opens a new structured
    /// wasm block (`if`, `block`, or `loop`) before recursing.
    fn nested(self) -> Self {
        Self {
            header: self.header,
            exit: self.exit,
            depth: self.depth + 1,
        }
    }
}

/// Target the wasm emitter uses to lower a `match` arm's `Jump(exit)` into a `br`
/// out of the single enclosing `block` that wraps the whole dispatch (see
/// `AirTerminator::Dispatch`). Analogous to [`LoopTarget`] but simpler: there is
/// no `loop`/back-edge, so a `Jump(exit)` is just `Br(depth)` to the block — no
/// `+1`. `depth` is the wasm-block depth from the current emission point to that
/// enclosing block, bumped by one for every structured instruction opened in
/// between (each arm test `if`, a range arm's inner `if`, …).
#[derive(Copy, Clone)]
struct DispatchTarget {
    /// The match join block — a `Jump` here leaves the dispatch via `Br(depth)`.
    exit: BlockId,
    depth: u32,
}

impl DispatchTarget {
    /// Increment the depth — used when the emitter opens a new structured wasm
    /// block before recursing into a match arm's body or test.
    fn nested(self) -> Self {
        Self {
            exit: self.exit,
            depth: self.depth + 1,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_block(
    mut block_id: BlockId,
    stop_at: Option<BlockId>,
    loop_target: Option<LoopTarget>,
    dispatch_exit: Option<DispatchTarget>,
    function: &AirFunction,
    blocks: &LookupMap<BlockId, &AirBlock>,
    emitted: &mut HashSet<BlockId>,
    body: &mut Function,
    type_map: &LookupMap<(Vec<ValType>, Vec<ValType>), u32>,
    import_count: u32,
    builtins: BuiltinImportIndices,
    ffi_imports: &LookupMap<String, u32>,
    static_data_offsets: &LookupMap<String, u32>,
) {
    // DoS hardening: structured-control-flow reconstruction used to recurse on the
    // *linear continuation* of each region — the merge block after an `if`, a jump
    // target, the block after a loop. For a function whose body is a long run of
    // sibling `if`s, the AIR is a chain of N branch blocks linked by `merge_block`,
    // so that continuation recursion was O(N) deep and overflowed the native stack
    // (a few hundred siblings was enough in a debug build). The continuation is now
    // followed by an explicit `loop`; only genuinely nested regions (an `if`'s
    // then/else arms, a loop body, a `match` arm body) still recurse, and that
    // depth is bounded by structural nesting rather than the sibling/arm count.
    //
    // `dispatch_exit` carries the innermost enclosing `match`'s join block (set by
    // `AirTerminator::Dispatch`): an arm body's `Jump(exit)` becomes a `br` OUT of
    // the single block that wraps the whole match, so the arm tests stay FLAT.
    loop {
        if Some(block_id) == stop_at || !emitted.insert(block_id) {
            return;
        }

        let Some(block) = blocks.get(&block_id).copied() else {
            body.instruction(&Instruction::Unreachable);
            return;
        };

        match &block.terminator {
            AirTerminator::Return(Some(var)) => {
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *var)));
                body.instruction(&Instruction::Return);
                return;
            }
            AirTerminator::Return(None) => {
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                emit_default_return(function.ret, body);
                body.instruction(&Instruction::Return);
                return;
            }
            AirTerminator::Jump(target) => {
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                if let Some(lt) = loop_target
                    && lt.header == *target
                {
                    // `continue` — re-enter the loop.
                    body.instruction(&Instruction::Br(lt.depth));
                    return;
                } else if let Some(lt) = loop_target
                    && lt.exit == *target
                {
                    // `break` — exit via the `block` wrapping the loop (one depth further out).
                    body.instruction(&Instruction::Br(lt.depth + 1));
                    return;
                } else if let Some(dt) = dispatch_exit
                    && dt.exit == *target
                {
                    // A `match` arm finished — `br` out of the block wrapping the
                    // whole dispatch, skipping the remaining arm tests.
                    body.instruction(&Instruction::Br(dt.depth));
                    return;
                } else if Some(*target) != stop_at {
                    // Linear continuation — iterate instead of recursing.
                    block_id = *target;
                    continue;
                } else {
                    return;
                }
            }
            AirTerminator::Loop {
                cond,
                body_block,
                exit_block,
            } => {
                body.instruction(&Instruction::Block(BlockType::Empty));
                body.instruction(&Instruction::Loop(BlockType::Empty));
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cond)));
                body.instruction(&Instruction::I32Eqz);
                // BrIf(1) — depth 1 targets the outer Block we just opened,
                // which is the loop's exit. (The Loop label is depth 0 from
                // here.)
                body.instruction(&Instruction::BrIf(1));
                // Inside the loop body, depth 0 IS this Loop's label. Any
                // descendant `if`/`block` will bump the depth via
                // `LoopTarget::nested()` before recursing.
                let body_target = LoopTarget {
                    header: block.id,
                    exit: *exit_block,
                    depth: 0,
                };
                // A `match` arm's `Jump(exit)` never appears inside a loop body (SIGIL
                // has no labeled break), so the enclosing dispatch target does not
                // reach here — drop it for the body. The post-loop continuation below
                // is back at this depth, so it keeps the original `dispatch_exit`.
                emit_block(
                    *body_block,
                    Some(block.id),
                    Some(body_target),
                    None,
                    function,
                    blocks,
                    emitted,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::End);
                body.instruction(&Instruction::End);

                if Some(*exit_block) != stop_at {
                    // Linear continuation — iterate instead of recursing.
                    block_id = *exit_block;
                    continue;
                } else {
                    return;
                }
            }
            AirTerminator::Branch {
                cond,
                then_block,
                else_block,
                merge_block,
            } => {
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                let merge = merge_block.or_else(|| {
                    merge_targets(
                        fallthrough_target(*then_block, blocks),
                        fallthrough_target(*else_block, blocks),
                        blocks,
                    )
                });
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cond)));
                body.instruction(&Instruction::If(BlockType::Empty));
                // We just opened an `if` — the loop label and the match dispatch
                // exit (if any) are now one depth further away from a descendant `Br`.
                let inner_loop_target = loop_target.map(LoopTarget::nested);
                let inner_dispatch = dispatch_exit.map(DispatchTarget::nested);
                emit_block(
                    *then_block,
                    merge,
                    inner_loop_target,
                    inner_dispatch,
                    function,
                    blocks,
                    emitted,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::Else);
                emit_block(
                    *else_block,
                    merge,
                    inner_loop_target,
                    inner_dispatch,
                    function,
                    blocks,
                    emitted,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::End);

                if dispatch_exit.is_some_and(|d| Some(d.exit) == merge) {
                    // The merge IS the enclosing `match`'s join block. Both arms of
                    // this `if` already `br`'d out of the dispatch block to reach it
                    // (an arm body ending in an `if` is the common case), so the join
                    // must be emitted ONCE after the dispatch block — not inlined
                    // here, which would bury post-match code (e.g. a loop back-edge)
                    // inside a single arm and corrupt control flow.
                    return;
                } else if let Some(target) = merge
                    && Some(target) != stop_at
                {
                    // Linear continuation (the merge block) — iterate instead of recursing.
                    block_id = target;
                    continue;
                } else if merge.is_none() {
                    // Both branches diverge (return/unreachable) — mark post-if as dead code
                    // Without this, Wasm validators reject the function because the code after
                    // the if/else is reachable but has no value on the stack for the function's
                    // return type.
                    body.instruction(&Instruction::Unreachable);
                    return;
                } else {
                    return;
                }
            }
            AirTerminator::Dispatch { start, exit } => {
                // Flat `match` dispatch: emit the scrutinee/setup stmts, open ONE
                // enclosing wasm `block`, then lower the arm-test chain inside it.
                // Each arm body's `Jump(exit)` becomes a `br` out of this block (via
                // `dispatch_exit`), so the arms are siblings at one nesting level
                // instead of a nested `if/else` cascade. Control resumes at `exit`
                // once the block closes.
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::Block(BlockType::Empty));
                // The new block adds one wasm frame, so any enclosing loop label is
                // one depth further out for the dispatch body. The dispatch body
                // gets its OWN fresh exit target at depth 0 (this block).
                emit_block(
                    *start,
                    Some(*exit),
                    loop_target.map(LoopTarget::nested),
                    Some(DispatchTarget {
                        exit: *exit,
                        depth: 0,
                    }),
                    function,
                    blocks,
                    emitted,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::End);

                if Some(*exit) != stop_at {
                    // Linear continuation — the code after the match.
                    block_id = *exit;
                    continue;
                } else {
                    return;
                }
            }
            AirTerminator::Unreachable => {
                emit_block_stmts(
                    block,
                    function,
                    body,
                    type_map,
                    import_count,
                    builtins,
                    ffi_imports,
                    static_data_offsets,
                );
                body.instruction(&Instruction::Unreachable);
                return;
            }
        }
    }
}

fn fallthrough_target(
    block_id: BlockId,
    blocks: &LookupMap<BlockId, &AirBlock>,
) -> Option<BlockId> {
    let block = blocks.get(&block_id).copied()?;
    match &block.terminator {
        AirTerminator::Return(_) | AirTerminator::Unreachable => None,
        AirTerminator::Jump(target) => {
            let target_block = blocks.get(target).copied()?;
            match &target_block.terminator {
                AirTerminator::Loop { exit_block, .. } => Some(*exit_block),
                _ => Some(*target),
            }
        }
        AirTerminator::Loop { exit_block, .. } => Some(*exit_block),
        // A `match` dispatch falls through to its join once the block closes.
        AirTerminator::Dispatch { exit, .. } => Some(*exit),
        AirTerminator::Branch {
            then_block,
            else_block,
            ..
        } => merge_targets(
            fallthrough_target(*then_block, blocks),
            fallthrough_target(*else_block, blocks),
            blocks,
        ),
    }
}

fn merge_targets(
    lhs: Option<BlockId>,
    rhs: Option<BlockId>,
    blocks: &LookupMap<BlockId, &AirBlock>,
) -> Option<BlockId> {
    match (lhs, rhs) {
        (Some(left), Some(right)) if left == right => Some(left),
        (Some(target), None) | (None, Some(target)) => Some(target),
        (None, None) => None,
        // The two branches fall through to DIFFERENT blocks. The real merge is the
        // FIRST block their linear successor chains share: a `Some(x)` arm flows
        // arm → extract-payload → body → exit (2+ hops) while a `None` arm flows
        // arm → exit (1 hop), so the fallthroughs differ even though both converge on
        // `exit`. The old code arbitrarily returned `left`, which mis-structured a
        // non-returning `match` (this branch is reached ONLY when `merge_block` is
        // `None` — i.e. for `match`; `if`/`else` always carry an explicit merge — so
        // returning-arm matches, whose fallthroughs are both `None`, are untouched).
        (Some(left), Some(right)) => first_common_successor(left, right, blocks),
    }
}

/// The first block reachable from BOTH `a` and `b` by following fallthrough chains —
/// the nearest common merge point of two branch arms. Each step uses `fallthrough_target`,
/// so it skips THROUGH a nested branch/if to that structure's own merge (a `Some(x)` arm
/// whose body contains an `if` still resolves to the match's `exit`). Cycle-guarded and
/// bounded; falls back to `a` (the old arbitrary-left behavior) if the chains never
/// converge. (No runaway mutual recursion with `merge_targets`: a well-formed `if`'s arms
/// converge on a single block — the `EQUAL` case — so the diff-arm path that re-enters
/// here is only the match dispatch itself, structurally shrinking each time.)
fn first_common_successor(
    a: BlockId,
    b: BlockId,
    blocks: &LookupMap<BlockId, &AirBlock>,
) -> Option<BlockId> {
    let mut a_chain = HashSet::new();
    let mut cur = Some(a);
    while let Some(c) = cur {
        if !a_chain.insert(c) || a_chain.len() > 1024 {
            break;
        }
        cur = fallthrough_target(c, blocks);
    }
    let mut seen = HashSet::new();
    let mut cur = Some(b);
    while let Some(c) = cur {
        if a_chain.contains(&c) {
            return Some(c);
        }
        if !seen.insert(c) || seen.len() > 1024 {
            break;
        }
        cur = fallthrough_target(c, blocks);
    }
    Some(a)
}

/// Wasm global index of the exported bump-allocation cursor.
const BUMP_PTR_GLOBAL: u32 = 0;

/// Reclaim regions only where global 0 is the established allocation cursor.
/// Actor and closure bodies retain static T254 checks but do not rewind memory.
fn region_reclaim_enabled(function: &AirFunction) -> bool {
    matches!(
        function.kind,
        AirFunctionKind::ModuleFunction | AirFunctionKind::ModuleInit
    )
}

#[allow(clippy::too_many_arguments)]
fn emit_stmt(
    stmt: &AirStmt,
    function: &AirFunction,
    body: &mut Function,
    type_map: &LookupMap<(Vec<ValType>, Vec<ValType>), u32>,
    import_count: u32,
    builtins: BuiltinImportIndices,
    ffi_imports: &LookupMap<String, u32>,
    static_data_offsets: &LookupMap<String, u32>,
) {
    match stmt {
        AirStmt::Assign { dst, val } => {
            emit_value(val, function, body, Some(*dst), static_data_offsets);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::SecurityRelease {
            dst,
            src,
            cap,
            cap_scratch,
            ..
        } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cap)));
            body.instruction(&Instruction::LocalSet(wasm_local_index(
                function,
                *cap_scratch,
            )));
        }
        AirStmt::Call { dst, func, args } => {
            for arg in args {
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *arg)));
            }
            body.instruction(&Instruction::Call(import_count + func.0));
            if let Some(dst) = dst {
                body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            }
        }
        AirStmt::OptionTry { dst, src } => {
            // PR OptTry / commit #3: real `?`-semantics for Option<T>.
            //
            // Mirrors the ResultTry emission below with INVERTED tag
            // semantics: Option's tag=1 means None (short-circuit),
            // tag=0 means Some (extract payload). PR B's stdlib
            // option.sigil declares variants in EXACT positional order
            // `Some(T), None` per N28-PRB → Some=variant 0, None=
            // variant 1. The `option_variant_indices_locked` unit test
            // (commit #4) re-asserts this against the stdlib file.
            //
            // Per N9-OptTry: this is a DISTINCT AirStmt variant from
            // ResultTry (not a type alias), so the two carriers'
            // inverted tag semantics can't be conflated.
            //
            //   ; if (*(src + 0) == OPTION_NONE_TAG) {   // None branch
            //   ;     return src;                        // propagate
            //   ; }
            //   ; dst = *(src + 4);                      // Some: extract
            //
            // Option layout (post-memory.rs flattening, N15-OptTry):
            //   offset 0 (i32, width 4): tag — 0 = Some, 1 = None
            //   offset 4 (T):            payload (Some's value)
            //
            // The enclosing function's return type is `Option<T>` which
            // lowers to `AirType::Ptr` (since Type::Named maps to Ptr
            // at lower_type), so returning `src` (a Ptr to the Option
            // struct) matches the function's wasm return shape.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::I32Load(mem_arg(0, 2)));
            // Test tag == OPTION_NONE_TAG (1); if so, return src as-is.
            // We compare equal-to-1 via i32.const + i32.eq.
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32Eq);
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::Return);
            body.instruction(&Instruction::End);
            // Some branch (fall-through): load payload from src+4 into dst.
            // Width/alignment dispatch identical to ResultTry below.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            let dst_ty = function.var_type(*dst);
            match dst_ty {
                AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
                    body.instruction(&Instruction::I32Load(mem_arg(4, 2)));
                }
                AirType::I64 | AirType::U64 => {
                    body.instruction(&Instruction::I64Load(mem_arg(4, 2)));
                }
                AirType::F64 => {
                    body.instruction(&Instruction::F64Load(mem_arg(4, 2)));
                }
                AirType::Unit => {
                    body.instruction(&Instruction::Drop);
                    body.instruction(&Instruction::I32Const(0));
                }
            }
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::ArrayOrSliceContains {
            dst,
            base_ptr,
            len,
            needle,
            idx,
            elem,
        } => {
            // Phase-1 completion: a bounded scan loop — `dst = false; for idx
            // in 0..len { if base[idx] == needle { dst = true; break } }`. This
            // rides the OptionTry/ResultTry "structured-wasm-inside-one-AirStmt"
            // hatch (intrinsic lowering is straight-line, so it cannot emit a
            // `Loop` terminator). Element-address math mirrors `LoadDynamic`
            // (`base + idx*elem_size`, the `+4` length-header skip baked into
            // `mem_arg` — for BOTH arrays and slices, since a slice's data_ptr
            // is not advanced past the underlying array's header); the Eq
            // opcode is by element width. `len` is loaded ONCE and `idx`
            // strictly increments ⇒ the loop provably terminates (fuel-exempt,
            // statically length-bounded — no Alloc/Call inside).
            let header_offset: u32 = 4;
            let elem_size = elem.width();
            // dst = false (0); idx = 0.
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::Block(BlockType::Empty)); // L_exit
            body.instruction(&Instruction::Loop(BlockType::Empty)); // L_cont
            // idx >= len → break to L_exit (depth 1 from the loop body).
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *len)));
            body.instruction(&Instruction::I32GeU);
            body.instruction(&Instruction::BrIf(1));
            // addr = base_ptr + idx * elem_size (header offset baked into the load).
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *base_ptr,
            )));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::I32Const(elem_size as i32));
            body.instruction(&Instruction::I32Mul);
            body.instruction(&Instruction::I32Add);
            // load element + compare to needle, by element width.
            match elem {
                AirType::Bool | AirType::Ptr | AirType::I32 | AirType::U32 => {
                    body.instruction(&Instruction::I32Load(mem_arg(header_offset, 2)));
                    body.instruction(&Instruction::LocalGet(wasm_local_index(function, *needle)));
                    body.instruction(&Instruction::I32Eq);
                }
                AirType::I64 | AirType::U64 => {
                    body.instruction(&Instruction::I64Load(mem_arg(header_offset, 3)));
                    body.instruction(&Instruction::LocalGet(wasm_local_index(function, *needle)));
                    body.instruction(&Instruction::I64Eq);
                }
                AirType::F64 => {
                    body.instruction(&Instruction::F64Load(mem_arg(header_offset, 3)));
                    body.instruction(&Instruction::LocalGet(wasm_local_index(function, *needle)));
                    body.instruction(&Instruction::F64Eq);
                }
                AirType::Unit => unreachable!("ICE: `.contains` on a unit-typed element"),
            }
            // if equal { dst = true; break }.
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            // depth 2 from inside the If: If=0, Loop=1, Block(L_exit)=2.
            body.instruction(&Instruction::Br(2));
            body.instruction(&Instruction::End); // close If
            // idx += 1; re-iterate (Br depth 0 = L_cont).
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32Add);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::Br(0));
            body.instruction(&Instruction::End); // close Loop
            body.instruction(&Instruction::End); // close Block (L_exit)
        }
        AirStmt::StrBytesEq {
            dst,
            lhs_data,
            lhs_len,
            rhs_data,
            rhs_len,
            idx,
        } => {
            // AG-S1-M: `dst = (lhs_len == rhs_len) && every byte matches`.
            //
            // NOTE the two differences from `ArrayOrSliceContains` above, both
            // of which are silent-wrong-answer traps if copied across:
            //
            //  1. The byte loads use offset 0, NOT the `+4` used there. A
            //     `str`'s `data_ptr` already points at byte 0 of the content
            //     (`substr` even sets it to `parent.data_ptr + start`); there
            //     is no length header to skip. A `+4` here would read four
            //     bytes past every string and fail only on inputs long enough
            //     to matter.
            //  2. The result sense is inverted: this starts from `len == len`
            //     and clears `dst` on the first mismatch, rather than starting
            //     false and setting true on a hit.
            //
            // Fuel: 1 up front so the O(1) length-mismatch path is not free,
            // then 1 per loop entry (including the exit test), matching what a
            // hand-written `while` byte loop pays per back-edge. `==` must not
            // buy a cheaper byte compare than writing the loop out.
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::Call(builtins.fuel_decrement));

            // dst = (lhs_len == rhs_len)
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *lhs_len)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *rhs_len)));
            body.instruction(&Instruction::I32Eq);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));

            // Only scan when the lengths agree.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::Block(BlockType::Empty)); // L_exit
            body.instruction(&Instruction::Loop(BlockType::Empty)); // L_cont

            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::Call(builtins.fuel_decrement));

            // idx >= lhs_len → every byte matched; leave dst = true.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *lhs_len)));
            body.instruction(&Instruction::I32GeU);
            body.instruction(&Instruction::BrIf(1));

            // lhs_data[idx] != rhs_data[idx] → dst = false; break.
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *lhs_data,
            )));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::I32Add);
            body.instruction(&Instruction::I32Load8U(mem_arg(0, 0)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *rhs_data,
            )));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::I32Add);
            body.instruction(&Instruction::I32Load8U(mem_arg(0, 0)));
            body.instruction(&Instruction::I32Ne);
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            // Depth from inside the If: If=0, Loop=1, Block(L_exit)=2.
            body.instruction(&Instruction::Br(2));
            body.instruction(&Instruction::End); // close If

            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32Add);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *idx)));
            body.instruction(&Instruction::Br(0));
            body.instruction(&Instruction::End); // close Loop
            body.instruction(&Instruction::End); // close Block (L_exit)
            body.instruction(&Instruction::End); // close If (lengths agree)
        }
        AirStmt::SliceOptionElem {
            dst,
            data_ptr,
            len,
            is_last,
            elem,
        } => {
            // Phase-1 completion: fill the pre-allocated `Option` struct by the
            // runtime length: `if len == 0 { tag = None } else { tag = Some;
            // payload@4 = data_ptr[idx] }` (idx = 0 for first, len-1 for last).
            // Replicates `lower_enum_construct`'s Option layout (tag@0,
            // payload@4) + the locked Some/None tags, so a downstream `match`
            // reads it like any user `Some(x)`/`None`.
            let elem_size = elem.width();
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *len)));
            body.instruction(&Instruction::I32Eqz); // len == 0 ?
            body.instruction(&Instruction::If(BlockType::Empty));
            // None: tag@0 = OPTION_NONE_TAG.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::I32Const(crate::air::OPTION_NONE_TAG));
            body.instruction(&Instruction::I32Store(mem_arg(0, 2)));
            body.instruction(&Instruction::Else);
            // Some: tag@0 = OPTION_SOME_TAG.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::I32Const(crate::air::OPTION_SOME_TAG));
            body.instruction(&Instruction::I32Store(mem_arg(0, 2)));
            // payload@4 = element at idx. Store base (dst) first, then the
            // loaded element value, then the width-dispatched store.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            // element address = data_ptr + idx*elem_size (idx = 0 | len-1).
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *data_ptr,
            )));
            if *is_last {
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *len)));
                body.instruction(&Instruction::I32Const(1));
                body.instruction(&Instruction::I32Sub);
                body.instruction(&Instruction::I32Const(elem_size as i32));
                body.instruction(&Instruction::I32Mul);
                body.instruction(&Instruction::I32Add);
            }
            // Load the element from the slice — `mem_arg` offset 4 is the
            // underlying-array length-header skip (a slice's data_ptr is not
            // advanced past it; align mirrors LoadDynamic). Then store into the
            // Option payload at offset 4 (align 2, matching the OptionTry
            // reader's payload load). The two `4`s are unrelated: one is the
            // array-header skip, the other the Option payload slot.
            match elem {
                AirType::Bool | AirType::Ptr | AirType::I32 | AirType::U32 => {
                    body.instruction(&Instruction::I32Load(mem_arg(4, 2)));
                    body.instruction(&Instruction::I32Store(mem_arg(4, 2)));
                }
                AirType::I64 | AirType::U64 => {
                    body.instruction(&Instruction::I64Load(mem_arg(4, 3)));
                    body.instruction(&Instruction::I64Store(mem_arg(4, 2)));
                }
                AirType::F64 => {
                    body.instruction(&Instruction::F64Load(mem_arg(4, 3)));
                    body.instruction(&Instruction::F64Store(mem_arg(4, 2)));
                }
                AirType::Unit => {
                    // A unit-typed element has no payload bytes; drop the base
                    // + addr we pushed and leave the Some tag (payload unused).
                    body.instruction(&Instruction::Drop);
                    body.instruction(&Instruction::Drop);
                }
            }
            body.instruction(&Instruction::End); // close If/Else
        }
        AirStmt::ResultTry { dst, src } => {
            // PR OptTry / commit #2: real `?`-semantics for Result<T, E>.
            //
            // Pre-PR-OptTry, ResultTry was a stub that set `dst = 0` and
            // ignored `src` — `?` type-checked but never actually short-
            // circuited at runtime. This emission implements the proper
            // unwrap-or-early-return shape:
            //
            //   if (*(src + IS_OK_OFFSET) == 0) {        // Err
            //       return src;                          // propagate up
            //   }
            //   dst = *(src + VALUE_OFFSET);             // Ok: extract T
            //
            // Result layout (post-memory.rs flattening, AG-PRB-B locked):
            //   offset 0 (i32): is_ok tag — 1 = Ok, 0 = Err
            //   offset 4 (T):   value payload — the Ok type's bytes
            //
            // Both offsets are sequential per `flatten_record`: is_ok
            // (i32, width 4) at 0, value at 4. No alignment padding (the
            // BumpAlloc is 8-byte aligned at the start, so the value at
            // offset 4 is 4-byte aligned, which is fine for i32; for i64
            // the load uses align=2^2=4 to match actual placement).
            //
            // Load is_ok from src+0.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::I32Load(mem_arg(0, 2)));
            // Test is_ok == 0 (Err); if so, return src as-is. The
            // enclosing function's wasm return type is i32 (Ptr) for
            // any `Result<T, E>` (lower_type maps Type::Named → Ptr).
            body.instruction(&Instruction::I32Eqz);
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::Return);
            body.instruction(&Instruction::End);
            // Ok branch (fall-through): load value from src+4 into dst.
            // Width/alignment determined by dst's AirType.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            let dst_ty = function.var_type(*dst);
            match dst_ty {
                AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
                    body.instruction(&Instruction::I32Load(mem_arg(4, 2)));
                }
                AirType::I64 | AirType::U64 => {
                    // i64 at offset 4 is 4-byte aligned, not 8 —
                    // match the actual placement to avoid alignment
                    // hint mismatch (wasm engines may degrade but
                    // not trap on alignment-hint mismatch).
                    body.instruction(&Instruction::I64Load(mem_arg(4, 2)));
                }
                AirType::F64 => {
                    body.instruction(&Instruction::F64Load(mem_arg(4, 2)));
                }
                AirType::Unit => {
                    // Unit-typed Ok value: drop the loaded base ptr;
                    // push 0 as a placeholder. dst's wasm local has
                    // no observable downstream use for Unit values.
                    body.instruction(&Instruction::Drop);
                    body.instruction(&Instruction::I32Const(0));
                }
            }
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::FuelDecrement { amount } => {
            body.instruction(&Instruction::I32Const(*amount as i32));
            body.instruction(&Instruction::Call(builtins.fuel_decrement));
        }
        AirStmt::MessageSend {
            target,
            handler,
            payload_buf,
            payload_len,
            ..
        } => {
            emit_message_call(
                *target,
                *handler,
                *payload_buf,
                *payload_len,
                function,
                body,
                builtins,
            );
            body.instruction(&Instruction::Call(
                builtins
                    .send
                    .expect("ICE: send import unavailable in current import set"),
            ));
        }
        AirStmt::MessageAsk {
            dst,
            target,
            handler,
            payload_buf,
            payload_len,
            timeout,
            ..
        } => {
            emit_message_call(
                *target,
                *handler,
                *payload_buf,
                *payload_len,
                function,
                body,
                builtins,
            );
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *timeout)));
            body.instruction(&Instruction::Call(
                builtins
                    .ask
                    .expect("ICE: ask import unavailable in current import set"),
            ));
            store_ask_result(*dst, function, body);
        }
        AirStmt::SerializeMessage {
            args,
            dst_buf,
            dst_len,
            ..
        } => emit_payload_serialize(args, *dst_buf, *dst_len, function, body, builtins),
        AirStmt::SpawnActor {
            dst,
            actor_type,
            caps,
            fuel_cap,
            supervision,
        } => {
            body.instruction(&Instruction::I32Const(actor_type.0 as i32));
            emit_cap_list_ptr(*dst, caps, function, body, builtins);
            body.instruction(&Instruction::I32Const(caps.len() as i32));
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *fuel_cap,
            )));
            // Encode supervision: 0 = Stop, n > 0 = Restart(max_restarts)
            let supervision_val = match supervision {
                AirSupervisionStrategy::Stop => 0,
                AirSupervisionStrategy::Restart { max_restarts } => *max_restarts as i32,
            };
            body.instruction(&Instruction::I32Const(supervision_val));
            body.instruction(&Instruction::Call(
                builtins
                    .spawn
                    .expect("ICE: spawn import unavailable in current import set"),
            ));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::PromoteBytes { dst, src, len } => {
            // PPS-2a: alloc_persistent(len) then copy `len` bytes from `src`. The import is
            // conditional-append, and `module_has_persistent_alloc` counts this statement, so a
            // module reaching here always has it.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *len)));
            body.instruction(&Instruction::Call(
                builtins
                    .alloc_persistent
                    .expect("ICE: PromoteBytes but alloc_persistent import not appended"),
            ));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *len)));
            body.instruction(&Instruction::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
        }
        AirStmt::BumpAlloc {
            dst,
            size_bytes,
            persistent,
            ..
        } => {
            body.instruction(&Instruction::I32Const(*size_bytes as i32));
            // PPS-0: same conditional-append channel as a persistent IntrinsicAlloc — only the
            // Call target differs, and only inside a state-backed instance.
            let target = if *persistent {
                builtins
                    .alloc_persistent
                    .expect("ICE: persistent BumpAlloc but alloc_persistent import not appended")
            } else {
                builtins.alloc
            };
            body.instruction(&Instruction::Call(target));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::IntrinsicAlloc {
            dst,
            size,
            persistent,
        } => {
            emit_i32_operand(*size, function, body);
            // AGG2b-2: a persistent alloc (a state-backed `Vec<scalar>` grow) calls the
            // conditional-append `alloc_persistent` import (B1 floor-raise); every other alloc
            // calls `alloc`. The size operand + I64ExtendI32U + LocalSet bytes are identical; only
            // the Call target differs, and only for a state-backed module (which HAS the import).
            let target = if *persistent {
                builtins
                    .alloc_persistent
                    .expect("ICE: persistent alloc but alloc_persistent import not appended")
            } else {
                builtins.alloc
            };
            body.instruction(&Instruction::Call(target));
            body.instruction(&Instruction::I64ExtendI32U);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::IntrinsicLoad8 { dst, ptr } => {
            emit_i32_operand(*ptr, function, body);
            body.instruction(&Instruction::I32Load8U(mem_arg(0, 0)));
            body.instruction(&Instruction::I64ExtendI32U);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::IntrinsicStore8 { ptr, val } => {
            emit_i32_operand(*ptr, function, body);
            emit_i64_byte_operand(*val, function, body);
            body.instruction(&Instruction::I64Store8(mem_arg(0, 0)));
        }
        AirStmt::IntrinsicCtEq { dst, lhs, rhs } => {
            // ct_eq(a, b) = (a ^ b) == 0. One I64Xor + I64Eqz; no branches.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *lhs)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *rhs)));
            body.instruction(&Instruction::I64Xor);
            body.instruction(&Instruction::I64Eqz);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::IntrinsicCtSelect {
            dst,
            cond,
            then_val,
            else_val,
        } => {
            // ct_select(c, t, f) = f XOR ((t XOR f) AND mask)
            //   mask = 0 - (c as i64) — all-ones if c==1, all-zeros if c==0.
            // No conditional branches. Never lowered to Wasm `select`
            // (which some backends compile to a CPU branch).
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *else_val,
            )));
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *then_val,
            )));
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *else_val,
            )));
            body.instruction(&Instruction::I64Xor); // then XOR else
            body.instruction(&Instruction::I64Const(0));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cond)));
            body.instruction(&Instruction::I64ExtendI32U);
            body.instruction(&Instruction::I64Sub); // 0 - (cond as i64) = mask
            body.instruction(&Instruction::I64And); // (then XOR else) AND mask
            body.instruction(&Instruction::I64Xor); // else XOR (...)
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::IntrinsicCtLt { dst, lhs, rhs } => {
            // ct_lt(a, b) = ((a - b) >> 63) & 1. Sign-bit extraction;
            // constant shift amount (63) so the shift is data-independent.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *lhs)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *rhs)));
            body.instruction(&Instruction::I64Sub);
            body.instruction(&Instruction::I64Const(63));
            body.instruction(&Instruction::I64ShrS);
            body.instruction(&Instruction::I32WrapI64);
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32And);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::CapRestrict {
            dst,
            src,
            restriction_mask,
        } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::I32Const(*restriction_mask as i32));
            body.instruction(&Instruction::Call(
                builtins
                    .cap_restrict
                    .expect("ICE: cap_restrict unavailable in current import set"),
            ));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::CapSplit { dst, src, amount } | AirStmt::CapDraw { dst, src, amount } => {
            // Both CapSplit and CapDraw lower to the same host import — at the
            // runtime layer, allocating a child cap with a given amount looks
            // identical. The semantic difference (parent-consumed vs parent-
            // preserved) lives entirely in ownership.rs. Reusing the import is
            // load-bearing for step 9's acceptance criterion #4: runtime LOC
            // stays unchanged.
            //
            // CSIR quantitative semantics requires an unconditional signed guard. This is not
            // elided for statically non-negative literals: one code shape keeps
            // proof classification out of code-generation decisions, while the
            // host repeats the check for untrusted Wasm callers.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *amount)));
            body.instruction(&Instruction::I64Const(0));
            body.instruction(&Instruction::I64LtS);
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::Unreachable);
            body.instruction(&Instruction::End);
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *amount)));
            body.instruction(&Instruction::Call(
                builtins
                    .cap_split
                    .expect("ICE: cap_split unavailable in current import set"),
            ));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::CapMint { dst, .. } => {
            // Capabilities-as-values: `mint` allocates a fresh capability id.
            // No args at the wasm ABI — `cap_name`/`params`/`target` are
            // compile-time/provenance only and erased here. The host import
            // registers the cap with the active actor and returns its id.
            body.instruction(&Instruction::Call(
                builtins
                    .cap_mint
                    .expect("ICE: cap_mint unavailable in current import set"),
            ));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::DeserializeMessage {
            src_buf,
            src_len,
            dst,
        } => {
            // Allocate space for the deserialized message
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src_len)));
            body.instruction(&Instruction::Call(builtins.alloc));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            // Copy from source buffer to allocated destination
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src_buf)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src_len)));
            body.instruction(&Instruction::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
        }
        AirStmt::StoreField {
            base_ptr,
            offset,
            val,
            ty,
        }
        | AirStmt::StateWrite {
            state_ptr: base_ptr,
            offset,
            val,
            ty,
            ..
        } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *base_ptr,
            )));
            // Handler payloads arrive as i64; wrap to i32 for memory32
            // addressing (mirrors the index wrap in LoadDynamic/StoreDynamic).
            let base_ty = function.var_type(*base_ptr);
            if base_ty == AirType::I64 || base_ty == AirType::U64 {
                body.instruction(&Instruction::I32WrapI64);
            }
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *val)));
            match ty {
                AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
                    body.instruction(&Instruction::I32Store(mem_arg(*offset, 2)));
                }
                AirType::I64 | AirType::U64 => {
                    body.instruction(&Instruction::I64Store(mem_arg(*offset, 3)));
                }
                AirType::F64 => {
                    body.instruction(&Instruction::F64Store(mem_arg(*offset, 3)));
                }
                AirType::Unit => {}
            }
        }
        AirStmt::LoadField {
            dst,
            base_ptr,
            offset,
            ty,
        }
        | AirStmt::StateRead {
            dst,
            state_ptr: base_ptr,
            offset,
            ty,
            ..
        } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function, *base_ptr,
            )));
            // Handler payloads arrive as i64; wrap to i32 for memory32
            // addressing (mirrors the index wrap in LoadDynamic/StoreDynamic).
            let base_ty = function.var_type(*base_ptr);
            if base_ty == AirType::I64 || base_ty == AirType::U64 {
                body.instruction(&Instruction::I32WrapI64);
            }
            match ty {
                AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
                    body.instruction(&Instruction::I32Load(mem_arg(*offset, 2)));
                }
                AirType::I64 | AirType::U64 => {
                    body.instruction(&Instruction::I64Load(mem_arg(*offset, 3)));
                }
                AirType::F64 => {
                    body.instruction(&Instruction::F64Load(mem_arg(*offset, 3)));
                }
                AirType::Unit => {
                    body.instruction(&Instruction::I32Const(0));
                }
            }
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::LoadDynamic {
            dst,
            base_ptr,
            index,
            elem_size,
            ty,
            offset,
        } => {
            if *ty == AirType::Unit {
                body.instruction(&Instruction::I32Const(0));
                body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            } else {
                // address = base_ptr + index * elem_size (header `offset` baked into mem_arg)
                body.instruction(&Instruction::LocalGet(wasm_local_index(
                    function, *base_ptr,
                )));
                {
                    // Same i64-base wrap as LoadField (handler-payload bases).
                    let base_ty = function.var_type(*base_ptr);
                    if base_ty == AirType::I64 || base_ty == AirType::U64 {
                        body.instruction(&Instruction::I32WrapI64);
                    }
                }
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *index)));
                // Wrap 64-bit index to i32 for Wasm memory math
                let index_ty = function.var_type(*index);
                if index_ty == AirType::I64 || index_ty == AirType::U64 {
                    body.instruction(&Instruction::I32WrapI64);
                }
                body.instruction(&Instruction::I32Const(*elem_size as i32));
                body.instruction(&Instruction::I32Mul);
                body.instruction(&Instruction::I32Add);
                match ty {
                    AirType::Bool | AirType::Ptr | AirType::I32 | AirType::U32 => {
                        body.instruction(&Instruction::I32Load(mem_arg(*offset, 2)));
                    }
                    AirType::I64 | AirType::U64 => {
                        body.instruction(&Instruction::I64Load(mem_arg(*offset, 3)));
                    }
                    AirType::F64 => {
                        body.instruction(&Instruction::F64Load(mem_arg(*offset, 3)));
                    }
                    AirType::Unit => unreachable!(),
                }
                body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            }
        }
        AirStmt::StoreDynamic {
            base_ptr,
            index,
            elem_size,
            val,
            ty,
            offset,
        } => {
            if *ty != AirType::Unit {
                body.instruction(&Instruction::LocalGet(wasm_local_index(
                    function, *base_ptr,
                )));
                {
                    // Same i64-base wrap as StoreField (handler-payload bases).
                    let base_ty = function.var_type(*base_ptr);
                    if base_ty == AirType::I64 || base_ty == AirType::U64 {
                        body.instruction(&Instruction::I32WrapI64);
                    }
                }
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *index)));
                // Wrap 64-bit index to i32 for Wasm memory math
                let idx_ty = function.var_type(*index);
                if idx_ty == AirType::I64 || idx_ty == AirType::U64 {
                    body.instruction(&Instruction::I32WrapI64);
                }
                body.instruction(&Instruction::I32Const(*elem_size as i32));
                body.instruction(&Instruction::I32Mul);
                body.instruction(&Instruction::I32Add);
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *val)));
                match ty {
                    AirType::Bool | AirType::Ptr | AirType::I32 | AirType::U32 => {
                        body.instruction(&Instruction::I32Store(mem_arg(*offset, 2)));
                    }
                    AirType::I64 | AirType::U64 => {
                        body.instruction(&Instruction::I64Store(mem_arg(*offset, 3)));
                    }
                    AirType::F64 => {
                        body.instruction(&Instruction::F64Store(mem_arg(*offset, 3)));
                    }
                    AirType::Unit => unreachable!(),
                }
            }
        }
        AirStmt::WrapI64 { dst, src } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::I32WrapI64);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::ExtendU32 { dst, src } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::I64ExtendI32U);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::SignExtendI32 { dst, src } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::I64ExtendI32S);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::TrapIf { cond } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cond)));
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::Unreachable);
            body.instruction(&Instruction::End);
        }
        // ── Wall 1 Step 2: Slot<Cap> linear container ──
        //
        // Wasm layout: 8-byte heap cell. Offset 0 = i32 tag (0=empty, 1=full).
        // Offset 4 = i32 cap_id (Sigil caps are bare i32 IDs at the wasm
        // boundary). Both fields cleared by SlotTake (INV-9 / MC-5).
        AirStmt::SlotNew { dst, cap_type: _ } => {
            // Allocate 8 bytes via the same builtin used by IntrinsicAlloc.
            body.instruction(&Instruction::I32Const(8));
            body.instruction(&Instruction::Call(builtins.alloc));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            // tag = 0 (empty)
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Store(mem_arg(0, 0)));
            // cap_id = 0 (placeholder)
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *dst)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Store(mem_arg(4, 0)));
        }
        AirStmt::SlotPut { slot, cap } => {
            // Trap if tag != 0 (already full). Mandated literal emission:
            // load tag, push 0, i32.ne, if/unreachable/end. The if's
            // condition is the live runtime mismatch — wasm reachability
            // sees that the trap MAY execute.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::I32Load(mem_arg(0, 0)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Ne);
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::Unreachable);
            body.instruction(&Instruction::End);
            // Set tag = 1 (full)
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::I32Const(1));
            body.instruction(&Instruction::I32Store(mem_arg(0, 0)));
            // Store cap_id at offset 4
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cap)));
            body.instruction(&Instruction::I32Store(mem_arg(4, 0)));
        }
        AirStmt::SlotTake { dst_cap, slot } => {
            // Trap if tag == 0 (empty). Same literal-emission discipline.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::I32Load(mem_arg(0, 0)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Eq);
            body.instruction(&Instruction::If(BlockType::Empty));
            body.instruction(&Instruction::Unreachable);
            body.instruction(&Instruction::End);
            // Read cap_id into dst_cap
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::I32Load(mem_arg(4, 0)));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst_cap)));
            // Clear BOTH tag AND cap_id (INV-9 / MC-5). The cap_id zero
            // prevents stale-pointer reads via out-of-band memory inspection.
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Store(mem_arg(0, 0)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *slot)));
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::I32Store(mem_arg(4, 0)));
        }
        AirStmt::CallIndirect {
            dst,
            signature,
            table_index,
            args,
        } => {
            // Push args (env_ptr first, then user args)
            for arg in args {
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *arg)));
            }
            // Push table index
            body.instruction(&Instruction::LocalGet(wasm_local_index(
                function,
                *table_index,
            )));
            // Look up the type index from the signature
            let wasm_params: Vec<ValType> = signature.0.iter().map(|ty| wasm_type(*ty)).collect();
            let wasm_results: Vec<ValType> = match signature.1 {
                AirType::Unit => vec![],
                ty => vec![wasm_type(ty)],
            };
            // Find the matching type index (must exist from the type section)
            let type_idx = type_map
                .get(&(wasm_params.clone(), wasm_results.clone()))
                .copied()
                .unwrap_or_else(|| {
                    // Register a new type if not found
                    // This shouldn't happen if types were pre-registered
                    panic!(
                        "ICE: call_indirect signature not found in type map: {:?} -> {:?}",
                        wasm_params, wasm_results
                    )
                });
            body.instruction(&Instruction::CallIndirect {
                type_index: type_idx,
                table_index: 0,
            });
            // Store result
            if let Some(dst) = dst {
                body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
            }
        }
        AirStmt::GrantBegin { .. } | AirStmt::GrantEnd { .. } => {
            // Grant markers are for audit trail — no-op in Wasm codegen
            // Runtime host imports for grant_begin/grant_end deferred to Phase 2B M5
        }
        AirStmt::Borrow { dst, src, .. } => {
            // Borrow is a pointer copy — identical to Assign(Var(src))
            // The distinction is for the ownership checker, not for Wasm
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *src)));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, *dst)));
        }
        AirStmt::ExternCall {
            dst,
            extern_name,
            args,
        } => {
            let (params, results) = ffi_signature(function, dst, args);
            let key = ffi_import_key(extern_name, &params, &results);
            let import_index = ffi_imports
                .get(&key)
                .copied()
                .unwrap_or_else(|| panic!("ICE: missing ffi import mapping for `{extern_name}`"));
            for arg in args {
                body.instruction(&Instruction::LocalGet(wasm_local_index(function, *arg)));
            }
            body.instruction(&Instruction::Call(import_index));
            if let Some(d) = dst {
                body.instruction(&Instruction::LocalSet(wasm_local_index(function, *d)));
            } else {
                for _ in 0..results.len() {
                    body.instruction(&Instruction::Drop);
                }
            }
        }
        // Snapshot and restore BUMP_PTR around module/tool regions. T254 guarantees
        // that rewinding cannot leave a live region allocation.
        AirStmt::RegionBegin { save_var, .. } => {
            if region_reclaim_enabled(function) {
                body.instruction(&Instruction::GlobalGet(BUMP_PTR_GLOBAL));
                body.instruction(&Instruction::LocalSet(wasm_local_index(
                    function, *save_var,
                )));
            }
        }
        AirStmt::RegionEnd {
            limit_var,
            save_var,
            ..
        } => {
            if region_reclaim_enabled(function) {
                let save_idx = wasm_local_index(function, *save_var);
                // Trap when net allocation at exit exceeds the declared limit. This is
                // not a peak bound because nested regions may already have reclaimed.
                body.instruction(&Instruction::GlobalGet(BUMP_PTR_GLOBAL));
                body.instruction(&Instruction::LocalGet(save_idx));
                body.instruction(&Instruction::I32Sub);
                body.instruction(&Instruction::LocalGet(wasm_local_index(
                    function, *limit_var,
                )));
                if matches!(
                    wasm_local_air_type(function, *limit_var),
                    AirType::I64 | AirType::U64
                ) {
                    body.instruction(&Instruction::I32WrapI64);
                }
                body.instruction(&Instruction::I32GtU);
                body.instruction(&Instruction::If(BlockType::Empty));
                body.instruction(&Instruction::Unreachable);
                body.instruction(&Instruction::End);
                // Rewind BUMP_PTR to reclaim the region.
                body.instruction(&Instruction::LocalGet(save_idx));
                body.instruction(&Instruction::GlobalSet(BUMP_PTR_GLOBAL));
            }
        }
    }
}

fn emit_message_call(
    target: VarId,
    handler: HandlerId,
    payload_buf: VarId,
    payload_len: VarId,
    function: &AirFunction,
    body: &mut Function,
    _builtins: BuiltinImportIndices,
) {
    body.instruction(&Instruction::LocalGet(wasm_local_index(function, target)));
    body.instruction(&Instruction::I32Const(handler.0 as i32));
    body.instruction(&Instruction::LocalGet(wasm_local_index(
        function,
        payload_buf,
    )));
    body.instruction(&Instruction::LocalGet(wasm_local_index(
        function,
        payload_len,
    )));
}

fn emit_payload_serialize(
    args: &[VarId],
    dst_buf: VarId,
    dst_len: VarId,
    function: &AirFunction,
    body: &mut Function,
    builtins: BuiltinImportIndices,
) {
    // Calculate total payload size
    let mut total_len = 0u32;
    for arg in args {
        total_len += function.var_type(*arg).width();
    }

    // Allocate buffer dynamically via $alloc
    body.instruction(&Instruction::I32Const(total_len as i32));
    body.instruction(&Instruction::Call(builtins.alloc));
    body.instruction(&Instruction::LocalSet(wasm_local_index(function, dst_buf)));

    // Serialize each arg into the allocated buffer
    let mut offset = 0u32;
    for arg in args {
        let ty = function.var_type(*arg);
        if ty == AirType::Unit {
            continue;
        }
        body.instruction(&Instruction::LocalGet(wasm_local_index(function, dst_buf)));
        body.instruction(&Instruction::LocalGet(wasm_local_index(function, *arg)));
        match ty {
            AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
                body.instruction(&Instruction::I32Store(mem_arg(offset, 2)));
            }
            AirType::I64 | AirType::U64 => {
                body.instruction(&Instruction::I64Store(mem_arg(offset, 3)));
            }
            AirType::F64 => {
                body.instruction(&Instruction::F64Store(mem_arg(offset, 3)));
            }
            AirType::Unit => {}
        }
        offset += ty.width();
    }

    body.instruction(&Instruction::I32Const(total_len as i32));
    body.instruction(&Instruction::LocalSet(wasm_local_index(function, dst_len)));
}

fn emit_cap_list_ptr(
    scratch: VarId,
    caps: &[VarId],
    function: &AirFunction,
    body: &mut Function,
    builtins: BuiltinImportIndices,
) {
    let total_size = (caps.len() * 4) as i32;
    let scratch_local = wasm_local_index(function, scratch);

    // Allocate buffer dynamically via $alloc
    body.instruction(&Instruction::I32Const(total_size));
    body.instruction(&Instruction::Call(builtins.alloc));
    body.instruction(&Instruction::LocalSet(scratch_local));

    // Store each capability ID into the allocated buffer
    let mut offset = 0u32;
    for cap in caps {
        body.instruction(&Instruction::LocalGet(scratch_local));
        body.instruction(&Instruction::LocalGet(wasm_local_index(function, *cap)));
        body.instruction(&Instruction::I32Store(mem_arg(offset, 2)));
        offset += 4;
    }

    // Push the buffer pointer onto the stack for $spawn's caps_ptr argument
    body.instruction(&Instruction::LocalGet(scratch_local));
}

fn mem_arg(offset: u32, align: u32) -> MemArg {
    MemArg {
        offset: offset as u64,
        align,
        memory_index: 0,
    }
}

fn emit_i32_operand(var: VarId, function: &AirFunction, body: &mut Function) {
    body.instruction(&Instruction::LocalGet(wasm_local_index(function, var)));
    if matches!(function.var_type(var), AirType::I64 | AirType::U64) {
        body.instruction(&Instruction::I32WrapI64);
    }
}

fn emit_i64_byte_operand(var: VarId, function: &AirFunction, body: &mut Function) {
    body.instruction(&Instruction::LocalGet(wasm_local_index(function, var)));
    match function.var_type(var) {
        AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
            body.instruction(&Instruction::I64ExtendI32U);
        }
        AirType::I64 | AirType::U64 => {}
        AirType::F64 | AirType::Unit => unreachable!("invalid byte operand type"),
    }
}

fn store_ask_result(dst: VarId, function: &AirFunction, body: &mut Function) {
    match function.var_type(dst) {
        AirType::I64 | AirType::U64 => {
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, dst)));
        }
        AirType::F64 => {
            body.instruction(&Instruction::F64ReinterpretI64);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, dst)));
        }
        AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
            body.instruction(&Instruction::I32WrapI64);
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, dst)));
        }
        AirType::Unit => {
            body.instruction(&Instruction::Drop);
            body.instruction(&Instruction::I32Const(0));
            body.instruction(&Instruction::LocalSet(wasm_local_index(function, dst)));
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_block_stmts(
    block: &AirBlock,
    function: &AirFunction,
    body: &mut Function,
    type_map: &LookupMap<(Vec<ValType>, Vec<ValType>), u32>,
    import_count: u32,
    builtins: BuiltinImportIndices,
    ffi_imports: &LookupMap<String, u32>,
    static_data_offsets: &LookupMap<String, u32>,
) {
    for stmt in &block.stmts {
        emit_stmt(
            stmt,
            function,
            body,
            type_map,
            import_count,
            builtins,
            ffi_imports,
            static_data_offsets,
        );
    }
}

fn emit_value(
    value: &AirValue,
    function: &AirFunction,
    body: &mut Function,
    dst: Option<VarId>,
    static_data_offsets: &LookupMap<String, u32>,
) {
    match value {
        AirValue::IntLit(value) => match dst
            .map(|var| function.var_type(var))
            .unwrap_or(AirType::I64)
        {
            // Unit-typed dst (the placeholder a Unit-returning intrinsic
            // statement initializes) is a wasm i32 local — see
            // `wasm_type(AirType::Unit) == I32`. Emit an i32 const, not i64,
            // or `LocalSet` rejects the module (type mismatch at load).
            AirType::Unit | AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
                body.instruction(&Instruction::I32Const(*value as i32));
            }
            AirType::I64 | AirType::U64 => {
                body.instruction(&Instruction::I64Const(*value));
            }
            AirType::F64 => {
                body.instruction(&Instruction::F64Const((*value as f64).into()));
            }
        },
        AirValue::FloatLit(value) => {
            body.instruction(&Instruction::F64Const((*value).into()));
        }
        AirValue::BoolLit(value) => {
            body.instruction(&Instruction::I32Const(i32::from(*value)));
        }
        AirValue::StrLit(value) => {
            let ptr = static_data_offsets
                .get(value)
                .copied()
                .unwrap_or_else(|| panic!("ICE: missing static data for string literal `{value}`"));
            body.instruction(&Instruction::I32Const(ptr as i32));
        }
        AirValue::UnitLit => {}
        AirValue::Var(var) => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *var)));
        }
        AirValue::Binary { lhs, op, rhs } => {
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *lhs)));
            body.instruction(&Instruction::LocalGet(wasm_local_index(function, *rhs)));
            match (op, function.var_type(*lhs)) {
                (BinaryOp::Add, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Add)
                }
                (BinaryOp::Sub, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Sub)
                }
                (BinaryOp::Mul, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Mul)
                }
                // Signedness-correct division + comparison: i64 uses signed
                // ops, u64 uses UNSIGNED (a u64 ≥ 2^63 must not be treated as
                // negative). Add/Sub/Mul/Eq/NotEq are sign-agnostic (one arm).
                (BinaryOp::Div, AirType::I64) => body.instruction(&Instruction::I64DivS),
                (BinaryOp::Div, AirType::U64) => body.instruction(&Instruction::I64DivU),
                (BinaryOp::Lt, AirType::I64) => body.instruction(&Instruction::I64LtS),
                (BinaryOp::Lt, AirType::U64) => body.instruction(&Instruction::I64LtU),
                (BinaryOp::LtEq, AirType::I64) => body.instruction(&Instruction::I64LeS),
                (BinaryOp::LtEq, AirType::U64) => body.instruction(&Instruction::I64LeU),
                (BinaryOp::Gt, AirType::I64) => body.instruction(&Instruction::I64GtS),
                (BinaryOp::Gt, AirType::U64) => body.instruction(&Instruction::I64GtU),
                (BinaryOp::GtEq, AirType::I64) => body.instruction(&Instruction::I64GeS),
                (BinaryOp::GtEq, AirType::U64) => body.instruction(&Instruction::I64GeU),
                (BinaryOp::Eq, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Eq)
                }
                (BinaryOp::NotEq, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Ne)
                }
                // PR AF: Ptr arithmetic via I32 lowering. Used by
                // `lower_slice_expr` to compute `data_ptr =
                // receiver_base + start * elem_size` for the slice
                // operator's view-semantics. Ptr is u32 at the wasm
                // memory-layer; same machine instruction.
                (BinaryOp::Add, AirType::I32 | AirType::U32 | AirType::Ptr) => {
                    body.instruction(&Instruction::I32Add)
                }
                (BinaryOp::Sub, AirType::I32 | AirType::U32 | AirType::Ptr) => {
                    body.instruction(&Instruction::I32Sub)
                }
                (BinaryOp::Mul, AirType::I32 | AirType::U32) => {
                    body.instruction(&Instruction::I32Mul)
                }
                (BinaryOp::Div, AirType::I32) => body.instruction(&Instruction::I32DivS),
                (BinaryOp::Div, AirType::U32) => body.instruction(&Instruction::I32DivU),
                (BinaryOp::Lt, AirType::I32) => body.instruction(&Instruction::I32LtS),
                (BinaryOp::Lt, AirType::U32) => body.instruction(&Instruction::I32LtU),
                (BinaryOp::LtEq, AirType::I32) => body.instruction(&Instruction::I32LeS),
                (BinaryOp::LtEq, AirType::U32) => body.instruction(&Instruction::I32LeU),
                (BinaryOp::Gt, AirType::I32) => body.instruction(&Instruction::I32GtS),
                (BinaryOp::Gt, AirType::U32) => body.instruction(&Instruction::I32GtU),
                (BinaryOp::GtEq, AirType::I32) => body.instruction(&Instruction::I32GeS),
                (BinaryOp::GtEq, AirType::U32) => body.instruction(&Instruction::I32GeU),
                (BinaryOp::Add, AirType::F64) => body.instruction(&Instruction::F64Add),
                (BinaryOp::Sub, AirType::F64) => body.instruction(&Instruction::F64Sub),
                (BinaryOp::Mul, AirType::F64) => body.instruction(&Instruction::F64Mul),
                (BinaryOp::Div, AirType::F64) => body.instruction(&Instruction::F64Div),
                (BinaryOp::Lt, AirType::F64) => body.instruction(&Instruction::F64Lt),
                (BinaryOp::LtEq, AirType::F64) => body.instruction(&Instruction::F64Le),
                (BinaryOp::Gt, AirType::F64) => body.instruction(&Instruction::F64Gt),
                (BinaryOp::GtEq, AirType::F64) => body.instruction(&Instruction::F64Ge),
                (BinaryOp::Eq, AirType::F64) => body.instruction(&Instruction::F64Eq),
                (BinaryOp::NotEq, AirType::F64) => body.instruction(&Instruction::F64Ne),
                (BinaryOp::Eq, _) => body.instruction(&Instruction::I32Eq),
                (BinaryOp::NotEq, _) => body.instruction(&Instruction::I32Ne),
                // Bit operators. Shifts pick arithmetic vs logical based on
                // the operand type's signedness — `i64 >> 1` is arithmetic
                // (sign-extending), `u64 >> 1` is logical (zero-filling).
                // `<<`, `&`, `|` are bit-pattern operations independent of
                // signedness, so one wasm instruction per width.
                (BinaryOp::Shl, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Shl)
                }
                (BinaryOp::Shr, AirType::I64) => body.instruction(&Instruction::I64ShrS),
                (BinaryOp::Shr, AirType::U64) => body.instruction(&Instruction::I64ShrU),
                (BinaryOp::BitAnd, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64And)
                }
                (BinaryOp::BitOr, AirType::I64 | AirType::U64) => {
                    body.instruction(&Instruction::I64Or)
                }
                (BinaryOp::Shl, AirType::I32 | AirType::U32) => {
                    body.instruction(&Instruction::I32Shl)
                }
                (BinaryOp::Shr, AirType::I32) => body.instruction(&Instruction::I32ShrS),
                (BinaryOp::Shr, AirType::U32) => body.instruction(&Instruction::I32ShrU),
                (BinaryOp::BitAnd, AirType::I32 | AirType::U32) => {
                    body.instruction(&Instruction::I32And)
                }
                (BinaryOp::BitOr, AirType::I32 | AirType::U32) => {
                    body.instruction(&Instruction::I32Or)
                }
                // `Bool` is i32-represented (comparison results are 0/1), so a
                // logical AND/OR of two conditions lowers to the i32 bitwise op.
                (BinaryOp::BitAnd, AirType::Bool) => body.instruction(&Instruction::I32And),
                (BinaryOp::BitOr, AirType::Bool) => body.instruction(&Instruction::I32Or),
                // Modulo: signed remainder for `i64`/`i32`, unsigned for
                // `u64`/`u32`. Wasm has no f64.rem — type-check rejects
                // float modulo via T054.
                (BinaryOp::Mod, AirType::I64) => body.instruction(&Instruction::I64RemS),
                (BinaryOp::Mod, AirType::U64) => body.instruction(&Instruction::I64RemU),
                (BinaryOp::Mod, AirType::I32) => body.instruction(&Instruction::I32RemS),
                (BinaryOp::Mod, AirType::U32) => body.instruction(&Instruction::I32RemU),
                (op, ty) => panic!("ICE: unsupported binary op {op:?} for type {ty:?}"),
            };
        }
        AirValue::RecordConstruct { .. } => {
            body.instruction(&Instruction::I32Const(0));
        }
    }
}

fn emit_default_return(ret: AirType, body: &mut Function) {
    match ret {
        AirType::Unit => {}
        AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => {
            body.instruction(&Instruction::I32Const(0));
        }
        AirType::I64 | AirType::U64 => {
            body.instruction(&Instruction::I64Const(0));
        }
        AirType::F64 => {
            body.instruction(&Instruction::F64Const(0.0_f64.into()));
        }
    }
}

fn wasm_local_index(function: &AirFunction, var: VarId) -> u32 {
    if let Some(index) = function.params.iter().position(|(id, _)| *id == var) {
        return index as u32;
    }

    let param_count = function.params.len() as u32;
    let local_index = function
        .locals
        .iter()
        .position(|(id, _)| *id == var)
        .unwrap_or_else(|| {
            panic!(
                "ICE: VarId({}) not found in function `{}`",
                var.0, function.name
            )
        }) as u32;
    param_count + local_index
}

/// Regions (DEF-2a PR-6): the `AirType` of a function param/local. Used by the LIMIT
/// exit-check for width-aware codegen — the declared limit defaults to `i64`, but the
/// byte count it is compared against is `i32`, so an `i64` limit is wrapped first.
/// Mirrors `wasm_local_index`'s param-then-local search order.
fn wasm_local_air_type(function: &AirFunction, var: VarId) -> AirType {
    if let Some((_, ty)) = function.params.iter().find(|(id, _)| *id == var) {
        return *ty;
    }
    function
        .locals
        .iter()
        .find(|(id, _)| *id == var)
        .map(|(_, ty)| *ty)
        .unwrap_or_else(|| {
            panic!(
                "ICE: VarId({}) type not found in function `{}`",
                var.0, function.name
            )
        })
}

fn wasm_type(ty: AirType) -> ValType {
    match ty {
        AirType::Unit => ValType::I32,
        AirType::I32 | AirType::U32 | AirType::Bool | AirType::Ptr => ValType::I32,
        AirType::I64 | AirType::U64 => ValType::I64,
        AirType::F64 => ValType::F64,
    }
}

#[cfg(test)]
mod tests {
    use sigil_abi::host_contract::{HOST_PROFILE_SECTION, HostProfileRequirement};
    use wasmparser::{Operator, Parser, Payload, TypeRef};

    use crate::compile_module;

    use super::{
        ALLOC_IMPORT_INDEX, ASK_IMPORT_INDEX, FUEL_DECREMENT_IMPORT_INDEX, RUNTIME_IMPORT_ALLOC,
        RUNTIME_IMPORT_ASK, RUNTIME_IMPORT_CAP_RESTRICT, RUNTIME_IMPORT_CAP_SPLIT,
        RUNTIME_IMPORT_FUEL_DECREMENT, RUNTIME_IMPORT_MODULE, RUNTIME_IMPORT_SEND,
        RUNTIME_IMPORT_SPAWN, SEND_IMPORT_INDEX, SPAWN_IMPORT_INDEX, WasmOutput,
        append_host_profile_requirement,
    };

    #[test]
    fn host_profile_requirement_uses_canonical_custom_section_framing_on_every_ring() {
        let header = b"\0asm\x01\0\0\0".to_vec();
        let mut output = WasmOutput {
            inner: header.clone(),
            outer: Some(header),
        };
        let requirement = HostProfileRequirement {
            fingerprint: [0xa5; 32],
        };
        append_host_profile_requirement(&mut output, requirement);

        for wasm in [
            output.inner.as_slice(),
            output
                .outer
                .as_deref()
                .expect("the fixture includes an outer module"),
        ] {
            let sections = Parser::new(0)
                .parse_all(wasm)
                .map(|payload| payload.expect("framed output must remain valid Wasm"))
                .filter_map(|payload| match payload {
                    Payload::CustomSection(section) if section.name() == HOST_PROFILE_SECTION => {
                        Some(section.data().to_vec())
                    }
                    _ => None,
                })
                .collect::<Vec<_>>();
            assert_eq!(sections, vec![requirement.encode().to_vec()]);
            assert_eq!(
                HostProfileRequirement::decode(&sections[0]),
                Ok(requirement)
            );
        }
    }

    #[test]
    fn emits_runtime_imports_for_actor_ops() {
        let compilation = compile_module(
            r#"
module sigil;
cap type Fuel {}

entry actor Main {
    state { fuel: Fuel }

    on Start(worker: ActorRef<Worker>) -> i64 {
        worker.send(Ping());
        let child = spawn::<Worker>(fuel);
        let count = worker.ask(GetCount(), timeout: 5);
        return count;
    }
}

actor Worker {
    init(fuel: Fuel) {}
    on Ping() {}
    on GetCount() -> i64 { return 1; }
}
"#,
        )
        .expect("message ops should compile");

        let mut imports = Vec::<(String, String)>::new();
        let mut call_indices = Vec::<u32>::new();

        for payload in Parser::new(0).parse_all(&compilation.wasm_inner) {
            match payload.expect("wasm payload should parse") {
                Payload::ImportSection(reader) => {
                    for import in reader.into_imports() {
                        let import = import.expect("import should parse");
                        if matches!(import.ty, TypeRef::Func(_)) {
                            imports.push((import.module.to_owned(), import.name.to_owned()));
                        }
                    }
                }
                Payload::CodeSectionEntry(body) => {
                    let mut operators = body
                        .get_operators_reader()
                        .expect("operator reader should parse");
                    while !operators.eof() {
                        if let Operator::Call { function_index } =
                            operators.read().expect("operator should parse")
                        {
                            call_indices.push(function_index);
                        }
                    }
                }
                _ => {}
            }
        }

        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_FUEL_DECREMENT.to_owned()
        )));
        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_SEND.to_owned()
        )));
        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_ASK.to_owned()
        )));
        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_SPAWN.to_owned()
        )));
        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_ALLOC.to_owned()
        )));
        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_CAP_RESTRICT.to_owned()
        )));
        assert!(imports.contains(&(
            RUNTIME_IMPORT_MODULE.to_owned(),
            RUNTIME_IMPORT_CAP_SPLIT.to_owned()
        )));
        assert!(call_indices.contains(&FUEL_DECREMENT_IMPORT_INDEX));
        assert!(call_indices.contains(&SEND_IMPORT_INDEX));
        assert!(call_indices.contains(&ASK_IMPORT_INDEX));
        assert!(call_indices.contains(&SPAWN_IMPORT_INDEX));
    }

    #[test]
    fn emits_static_data_for_string_literals() {
        let compilation = compile_module(
            r#"
module sigil;
fn label() -> str {
    return "hello";
}
"#,
        )
        .expect("string literal module should compile");

        let mut saw_data = false;
        let mut saw_hello = false;
        for payload in Parser::new(0).parse_all(&compilation.wasm_inner) {
            if let Payload::DataSection(reader) = payload.expect("wasm payload should parse") {
                saw_data = true;
                for segment in reader {
                    let segment = segment.expect("data segment should parse");
                    if segment.data == b"hello" {
                        saw_hello = true;
                    }
                }
            }
        }

        assert!(saw_data, "string literals should emit a data section");
        assert!(saw_hello, "expected a data segment containing `hello`");
    }

    #[test]
    fn emits_byte_intrinsic_wasm_ops() {
        let compilation = compile_module(
            r#"
module tool;
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {
    let out_ptr = alloc(input_len);
    let first = load8(input_ptr);
    store8(out_ptr, first);
    return out_ptr * 4294967296 + 1;
}
"#,
        )
        .expect("byte intrinsics should compile");

        let mut saw_alloc_call = false;
        let mut saw_load8 = false;
        let mut saw_store8 = false;

        for payload in Parser::new(0).parse_all(&compilation.wasm_inner) {
            if let Payload::CodeSectionEntry(body) = payload.expect("wasm payload should parse") {
                let mut operators = body
                    .get_operators_reader()
                    .expect("operator reader should parse");
                while !operators.eof() {
                    match operators.read().expect("operator should parse") {
                        Operator::Call { function_index }
                            if function_index == ALLOC_IMPORT_INDEX =>
                        {
                            saw_alloc_call = true;
                        }
                        Operator::I32Load8U { .. } => {
                            saw_load8 = true;
                        }
                        Operator::I64Store8 { .. } => {
                            saw_store8 = true;
                        }
                        _ => {}
                    }
                }
            }
        }

        assert!(
            saw_alloc_call,
            "expected alloc intrinsic to call the runtime alloc import"
        );
        assert!(saw_load8, "expected load8 intrinsic to emit i32.load8_u");
        assert!(saw_store8, "expected store8 intrinsic to emit i64.store8");
    }
}
