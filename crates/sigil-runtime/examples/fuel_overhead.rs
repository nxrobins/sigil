//! Fuel-instrumentation runtime overhead micro-benchmark (one-shot, doc-published).
//!
//! Measures what the fuel metering costs at RUN time for one metering-heavy
//! tool, `tools/task098_levenshtein_distance.sigil`, on seeded-random inputs.
//! Compile time is what `examples/throughput.rs` in `sigil-compiler` measures;
//! this harness measures the forge step that follows it: a fresh `Store`, a
//! fresh `Instance`, the input copy, and the metered run. Output is a markdown
//! summary plus the raw samples; authors paste the summary into PERFORMANCE.md.
//!
//! Two modules, four conditions, plus a fidelity pair:
//!
//! - `A0` is the tool's wasm exactly as `sigil forge` compiles it
//!   (`compile_tool_with_limits_and_context` with the default limits and
//!   context, the same call `crates/sigil-cli/src/forge.rs` makes).
//! - `A1` is `A0` with every `call 0` (the `sigil.fuel_decrement` import,
//!   always preceded by an `i32.const`) replaced by `drop`. Only the code
//!   section is re-encoded; every other section is copied byte-for-byte, and
//!   the result is validated and shown to produce the same output bytes.
//! - `A` = `A0` through the shipped `execute_ephemeral` (host-call decrements
//!   plus the Wasmtime `consume_fuel` backstop).
//! - `B` = `A1` through the shipped `execute_ephemeral` (backstop only).
//! - `C` = `A1` on a bench-only mirror of that path with Wasmtime fuel OFF
//!   (the fuel-free baseline).
//! - `D` = `A0` on the mirror with Wasmtime fuel OFF.
//! - `A'`/`B'` = `A0`/`A1` on the mirror with Wasmtime fuel ON, so the
//!   mirror's agreement with the shipped path is itself a reported number.
//!
//! The shipped runtime has no seam that disables the backstop, and it must not
//! grow one: `C`/`D` therefore run on a mirror built HERE, from its own
//! `Engine`/`Store`/`Linker`, shaped like `execute_ephemeral_inner` (same fuel
//! shim, same bump allocator, same memory wall) but with unused imports bound
//! to traps. Nothing in the shipped `sigil forge` path changes.
//!
//! Every block reports its median (the PERFORMANCE.md convention) AND its
//! minimum, and the derived table is emitted on both. Why the minimum: a block
//! that runs to the 500-sample ceiling spans tens of seconds, and on a host
//! with other work the median then carries that work while the minimum is the
//! uncontended cost — on the 2026-09-20 host the shipped A0 block at L=1000
//! had a median 25% above the mirror's converged block but the same minimum
//! to 1%. The report says which host state each number was taken in.
//!
//! Failure direction: any sample that does not return `Ok` with the expected
//! output aborts the run — a trapped or fuel-exhausted sample measures nothing.
//! A debug-profile build is refused unless `--allow-debug` is passed.
//!
//!     cargo run --release --no-default-features -p sigil-runtime \
//!         --example fuel_overhead -- --out DIR [--seed N] [--lengths 0,100,500,1000]

use std::convert::Infallible;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use sha2::{Digest, Sha256};
use sigil_compiler::{
    CompileLimits, CompilerContext, compile_tool, compile_tool_with_limits_and_context,
};
use sigil_runtime::{IoGrants, execute_ephemeral};
use wasm_encoder::reencode::{self, Reencode};
use wasm_encoder::{CodeSection, Instruction, RawSection};
use wasmparser::{ElementItems, Operator, Parser, Payload, Validator};
use wasmtime::{
    Caller, Config, Engine, Linker, Module, Store, StoreLimits, StoreLimitsBuilder, Val, ValType,
};

/// One discarded call per block (PERFORMANCE.md rule).
const WARMUP_RUNS: usize = 1;
/// Trailing window for the convergence test (PERFORMANCE.md rule).
const MIN_SAMPLES: usize = 30;
/// Sample ceiling per block (PERFORMANCE.md rule).
const DEFAULT_MAX_SAMPLES: usize = 500;
/// Converged when the trailing-window CV is below this (percent).
const CV_CONVERGED: f64 = 5.0;
/// Flagged ✗ at or above this (percent), as the throughput bench does.
const CV_DROP: f64 = 20.0;
/// Arbitrary, recorded in the report; `--seed` overrides it.
const DEFAULT_SEED: u64 = 0x5347_494c_2d44_3500;
/// Two strings of this many `[a-z]` bytes each, joined by one `\n`.
const DEFAULT_LENGTHS: &[usize] = &[0, 100, 500, 1000];
/// Cold (Wasmtime-compile-inclusive) first calls measured per module.
const DEFAULT_COLD_REPEATS: usize = 3;
/// Mirrors `MAX_WASM_FUEL` in `ephemeral.rs`: the backstop budget.
const MAX_WASM_FUEL: u64 = 10_000_000_000;
/// Mirrors `MAX_GUEST_MEMORY_BYTES` in `ephemeral.rs`: the 16 MB wall.
const MAX_GUEST_MEMORY_BYTES: usize = 16 * 1024 * 1024;
const WASM_PAGE_SIZE: u64 = 64 * 1024;
/// `sigil.fuel_decrement` is function index 0 in both import sets (wasm.rs).
const FUEL_DECREMENT_IMPORT_INDEX: u32 = 0;
/// A generous calibration budget; the measured budget is 2x the calibrated use.
const CALIBRATION_BUDGET: u64 = u64::MAX / 4;

fn main() {
    if let Err(message) = run() {
        eprintln!("fuel_overhead: {message}");
        std::process::exit(1);
    }
}

struct Args {
    out: PathBuf,
    seed: u64,
    lengths: Vec<usize>,
    max_samples: usize,
    cold_repeats: usize,
    allow_debug: bool,
}

fn parse_args() -> Result<Args, String> {
    let mut out = None;
    let mut seed = DEFAULT_SEED;
    let mut lengths = DEFAULT_LENGTHS.to_vec();
    let mut max_samples = DEFAULT_MAX_SAMPLES;
    let mut cold_repeats = DEFAULT_COLD_REPEATS;
    let mut allow_debug = false;
    let mut argv = std::env::args().skip(1);
    while let Some(arg) = argv.next() {
        let mut value = |flag: &str| -> Result<String, String> {
            argv.next()
                .ok_or_else(|| format!("{flag} requires a value"))
        };
        match arg.as_str() {
            "--out" => out = Some(PathBuf::from(value("--out")?)),
            "--seed" => {
                seed = value("--seed")?
                    .parse()
                    .map_err(|e| format!("--seed: {e}"))?;
            }
            "--lengths" => {
                lengths = value("--lengths")?
                    .split(',')
                    .map(|s| {
                        s.trim()
                            .parse::<usize>()
                            .map_err(|e| format!("--lengths: {e}"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
            }
            "--max-samples" => {
                max_samples = value("--max-samples")?
                    .parse()
                    .map_err(|e| format!("--max-samples: {e}"))?;
            }
            "--cold-repeats" => {
                cold_repeats = value("--cold-repeats")?
                    .parse()
                    .map_err(|e| format!("--cold-repeats: {e}"))?;
            }
            "--allow-debug" => allow_debug = true,
            other => return Err(format!("unknown argument {other}; see the module doc")),
        }
    }
    let out = out.ok_or("--out DIR is required")?;
    if !lengths.contains(&0) {
        return Err("--lengths must include 0: the L=0 run is the fixed per-call cost".into());
    }
    if max_samples < MIN_SAMPLES {
        return Err(format!("--max-samples must be at least {MIN_SAMPLES}"));
    }
    Ok(Args {
        out,
        seed,
        lengths,
        max_samples,
        cold_repeats,
        allow_debug,
    })
}

// ---------------------------------------------------------------------------
// Seeded randomness: SplitMix64. Modulo bias on `below(26)` and on the block
// shuffle is far below anything this benchmark can resolve, and the seed is
// recorded so every input is reproducible by hash.
// ---------------------------------------------------------------------------

struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() {
            let j = self.below(i as u64 + 1) as usize;
            items.swap(i, j);
        }
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

// ---------------------------------------------------------------------------
// Workload: two random [a-z] strings joined by '\n', plus the host-side
// Levenshtein distance the tool's decimal output must equal.
// ---------------------------------------------------------------------------

struct Workload {
    len: usize,
    input: Vec<u8>,
    input_sha256: String,
    expected: Vec<u8>,
}

fn random_lowercase(rng: &mut SplitMix64, len: usize) -> Vec<u8> {
    (0..len).map(|_| b'a' + rng.below(26) as u8).collect()
}

/// Independent reference: the classic two-row DP, so the tool's answer is
/// checked against something that shares no code with it.
fn levenshtein(left: &[u8], right: &[u8]) -> usize {
    let mut prev: Vec<usize> = (0..=right.len()).collect();
    let mut curr = vec![0usize; right.len() + 1];
    for (i, &l) in left.iter().enumerate() {
        curr[0] = i + 1;
        for (j, &r) in right.iter().enumerate() {
            let cost = usize::from(l != r);
            curr[j + 1] = (prev[j + 1] + 1).min(curr[j] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[right.len()]
}

fn make_workload(rng: &mut SplitMix64, len: usize) -> Workload {
    let left = random_lowercase(rng, len);
    let right = random_lowercase(rng, len);
    let mut input = left.clone();
    input.push(b'\n');
    input.extend_from_slice(&right);
    let expected = levenshtein(&left, &right).to_string().into_bytes();
    Workload {
        len,
        input_sha256: sha256_hex(&input),
        input,
        expected,
    }
}

// ---------------------------------------------------------------------------
// Modules. A0 is the shipped compile; A1 drops every fuel_decrement call.
// ---------------------------------------------------------------------------

struct A0 {
    bytes: Vec<u8>,
    function_count: usize,
    static_fuel_budget: u64,
    imports: Vec<String>,
}

fn build_a0(source: &str) -> Result<A0, String> {
    // The exact call `sigil forge` makes (crates/sigil-cli/src/forge.rs).
    let forge = compile_tool_with_limits_and_context(
        source,
        &CompileLimits::default(),
        &CompilerContext::default(),
    )
    .map_err(|e| format!("compile_tool_with_limits_and_context: {e:?}"))?;
    // The plain `compile_tool` entry the runtime tests use must agree byte-for-byte.
    let plain = compile_tool(source).map_err(|e| format!("compile_tool: {e:?}"))?;
    if plain.wasm != forge.wasm {
        return Err("compile_tool and the forge entry point disagree on the tool bytes".into());
    }
    let imports = Parser::new(0)
        .parse_all(&forge.wasm)
        .filter_map(|payload| match payload {
            Ok(Payload::ImportSection(reader)) => Some(reader),
            _ => None,
        })
        .flat_map(|reader| {
            reader
                .into_imports()
                .map(|import| {
                    import
                        .map(|i| format!("{}.{}", i.module, i.name))
                        .map_err(|e| e.to_string())
                })
                .collect::<Vec<_>>()
        })
        .collect::<Result<Vec<_>, _>>()?;
    match imports.first().map(String::as_str) {
        Some("sigil.fuel_decrement") => {}
        // Fail closed: the rewrite below targets index 0 by construction.
        other => {
            return Err(format!(
                "import 0 is {other:?}, not sigil.fuel_decrement; the call-0 rewrite would be wrong"
            ));
        }
    }
    Ok(A0 {
        bytes: forge.wasm,
        function_count: forge.function_count,
        static_fuel_budget: forge.fuel_budget,
        imports,
    })
}

/// A `Reencode` that turns `call 0` into `drop` and counts what it sees.
/// Every fuel_decrement call follows an `i32.const`, so `drop` keeps the body
/// well-typed; the validator below is the proof, this is only the rewrite.
#[derive(Default)]
struct DropFuelCalls {
    replaced: usize,
    ref_func_zero: usize,
    return_call_zero: usize,
}

impl Reencode for DropFuelCalls {
    type Error = Infallible;

    fn instruction<'a>(
        &mut self,
        arg: Operator<'a>,
    ) -> Result<Instruction<'a>, reencode::Error<Infallible>> {
        match arg {
            Operator::Call {
                function_index: FUEL_DECREMENT_IMPORT_INDEX,
            } => {
                self.replaced += 1;
                Ok(Instruction::Drop)
            }
            Operator::RefFunc {
                function_index: FUEL_DECREMENT_IMPORT_INDEX,
            } => {
                self.ref_func_zero += 1;
                reencode::utils::instruction(self, arg)
            }
            Operator::ReturnCall {
                function_index: FUEL_DECREMENT_IMPORT_INDEX,
            } => {
                self.return_call_zero += 1;
                reencode::utils::instruction(self, arg)
            }
            other => reencode::utils::instruction(self, other),
        }
    }
}

struct A1 {
    bytes: Vec<u8>,
    replaced_calls: usize,
    functions: usize,
    sections_copied: usize,
}

fn build_a1(a0: &[u8]) -> Result<A1, String> {
    let mut out = wasm_encoder::Module::new();
    let mut pending_code: Option<CodeSection> = None;
    let mut rewriter = DropFuelCalls::default();
    let mut functions = 0usize;
    let mut sections_copied = 0usize;
    for payload in Parser::new(0).parse_all(a0) {
        let payload = payload.map_err(|e| format!("parse A0: {e}"))?;
        // The code section is emitted in place once its entries are consumed.
        if !matches!(payload, Payload::CodeSectionEntry(_))
            && let Some(code) = pending_code.take()
        {
            out.section(&code);
        }
        match payload {
            Payload::Version { .. } | Payload::End(_) => {}
            Payload::CodeSectionStart { .. } => pending_code = Some(CodeSection::new()),
            Payload::CodeSectionEntry(body) => {
                let code = pending_code
                    .as_mut()
                    .ok_or("code entry before the code section header")?;
                reencode::utils::parse_function_body(&mut rewriter, code, body)
                    .map_err(|e| format!("re-encode function {functions}: {e}"))?;
                functions += 1;
            }
            Payload::ElementSection(reader) => {
                // A table entry for index 0 would let `call_indirect` reach the
                // decrement in A1; fail closed rather than measure a half-stripped module.
                for element in reader.clone() {
                    let element = element.map_err(|e| e.to_string())?;
                    match element.items {
                        ElementItems::Functions(funcs) => {
                            for func in funcs {
                                if func.map_err(|e| e.to_string())? == FUEL_DECREMENT_IMPORT_INDEX {
                                    return Err("an element segment references function 0".into());
                                }
                            }
                        }
                        ElementItems::Expressions(_, _) => {
                            return Err("A0 has expression-initialised element segments".into());
                        }
                    }
                }
                let (id, range) = Payload::ElementSection(reader)
                    .as_section()
                    .ok_or("element section without a range")?;
                out.section(&RawSection {
                    id,
                    data: &a0[range],
                });
                sections_copied += 1;
            }
            other => {
                let (id, range) = other
                    .as_section()
                    .ok_or_else(|| format!("unhandled payload {other:?}"))?;
                out.section(&RawSection {
                    id,
                    data: &a0[range],
                });
                sections_copied += 1;
            }
        }
    }
    if let Some(code) = pending_code.take() {
        out.section(&code);
    }
    if rewriter.replaced == 0 {
        // Anti-stub: a rewrite that found nothing to replace is a broken rewrite.
        return Err("no `call 0` found in A0; the rewrite matched nothing".into());
    }
    if rewriter.ref_func_zero != 0 || rewriter.return_call_zero != 0 {
        return Err(format!(
            "A0 reaches function 0 other than by `call` (ref.func {} / return_call {})",
            rewriter.ref_func_zero, rewriter.return_call_zero
        ));
    }
    let bytes = out.finish();
    Validator::new()
        .validate_all(&bytes)
        .map_err(|e| format!("A1 does not validate: {e}"))?;
    let calls_left = count_calls_to(&bytes, FUEL_DECREMENT_IMPORT_INDEX)?;
    if calls_left != 0 {
        return Err(format!("A1 still holds {calls_left} calls to function 0"));
    }
    let calls_before = count_calls_to(a0, FUEL_DECREMENT_IMPORT_INDEX)?;
    if calls_before != rewriter.replaced {
        return Err(format!(
            "independent count of `call 0` in A0 ({calls_before}) != replaced ({})",
            rewriter.replaced
        ));
    }
    let a0_sections = non_code_section_digests(a0)?;
    let a1_sections = non_code_section_digests(&bytes)?;
    if a0_sections != a1_sections {
        return Err("A1's non-code sections are not byte-identical to A0's".into());
    }
    Ok(A1 {
        bytes,
        replaced_calls: rewriter.replaced,
        functions,
        sections_copied,
    })
}

/// Independent detector for the rewrite: a plain operator scan, no re-encoding.
fn count_calls_to(wasm: &[u8], index: u32) -> Result<usize, String> {
    let mut count = 0usize;
    for payload in Parser::new(0).parse_all(wasm) {
        if let Payload::CodeSectionEntry(body) = payload.map_err(|e| e.to_string())? {
            let reader = body.get_operators_reader().map_err(|e| e.to_string())?;
            for op in reader {
                if let Operator::Call { function_index } = op.map_err(|e| e.to_string())?
                    && function_index == index
                {
                    count += 1;
                }
            }
        }
    }
    Ok(count)
}

/// `(section id, sha256 of its contents)` for every section except code, in order.
fn non_code_section_digests(wasm: &[u8]) -> Result<Vec<(u8, String)>, String> {
    let mut out = Vec::new();
    for payload in Parser::new(0).parse_all(wasm) {
        let payload = payload.map_err(|e| e.to_string())?;
        if matches!(payload, Payload::CodeSectionStart { .. }) {
            continue;
        }
        if let Some((id, range)) = payload.as_section() {
            out.push((id, sha256_hex(&wasm[range])));
        }
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// The bench-only mirror of `execute_ephemeral_inner`, with the backstop
// switchable. Same fuel shim semantics, same bump allocator, same 16 MB wall.
// ---------------------------------------------------------------------------

struct MirrorData {
    fuel_remaining: u64,
    fuel_exhausted: bool,
    memory_budget: usize,
    limits: StoreLimits,
}

struct Mirror {
    engine: Engine,
    module: Module,
    fuel_on: bool,
}

impl Mirror {
    fn new(wasm: &[u8], fuel_on: bool) -> Result<Self, String> {
        let mut config = Config::new();
        config.consume_fuel(fuel_on);
        let engine = Engine::new(&config).map_err(|e| e.to_string())?;
        let module = Module::from_binary(&engine, wasm).map_err(|e| e.to_string())?;
        Ok(Self {
            engine,
            module,
            fuel_on,
        })
    }

    fn run(&self, input: &[u8], fuel_budget: u64) -> Result<(Vec<u8>, u64), String> {
        let mut linker: Linker<MirrorData> = Linker::new(&self.engine);
        linker
            .func_wrap(
                "sigil",
                "fuel_decrement",
                |mut caller: Caller<'_, MirrorData>, amount: i32| -> wasmtime::Result<()> {
                    let data = caller.data_mut();
                    let cost = u64::try_from(amount)
                        .map_err(|_| wasmtime::Error::msg("fuel decrement must be non-negative"))?;
                    if cost > data.fuel_remaining {
                        data.fuel_exhausted = true;
                        return Err(wasmtime::Error::msg("fuel exhausted"));
                    }
                    data.fuel_remaining -= cost;
                    Ok(())
                },
            )
            .map_err(|e| e.to_string())?;
        linker
            .func_wrap(
                "sigil",
                "alloc",
                |mut caller: Caller<'_, MirrorData>, size: i32| -> wasmtime::Result<i32> {
                    let size = u32::try_from(size)
                        .map_err(|_| wasmtime::Error::msg("alloc size must be non-negative"))?;
                    let memory = match caller.get_export("memory") {
                        Some(wasmtime::Extern::Memory(memory)) => memory,
                        _ => return Err(wasmtime::Error::msg("no memory export")),
                    };
                    let bump = match caller.get_export("BUMP_PTR") {
                        Some(wasmtime::Extern::Global(global)) => global,
                        _ => return Err(wasmtime::Error::msg("no BUMP_PTR export")),
                    };
                    let ptr = alloc_from_bump(&memory, &bump, &mut caller, size)
                        .map_err(wasmtime::Error::msg)?;
                    Ok(ptr as i32)
                },
            )
            .map_err(|e| e.to_string())?;
        // Every other import traps if reached; this workload reaches none.
        linker
            .define_unknown_imports_as_traps(&self.module)
            .map_err(|e| e.to_string())?;
        // The shipped path validates the grants on every call; keep that cost.
        IoGrants::default().validate().map_err(|e| e.to_string())?;
        let mut store = Store::new(
            &self.engine,
            MirrorData {
                fuel_remaining: fuel_budget,
                fuel_exhausted: false,
                memory_budget: MAX_GUEST_MEMORY_BYTES,
                limits: StoreLimitsBuilder::new()
                    .memory_size(MAX_GUEST_MEMORY_BYTES)
                    .memories(1)
                    .instances(1)
                    .trap_on_grow_failure(true)
                    .build(),
            },
        );
        store.limiter(|data| &mut data.limits);
        if self.fuel_on {
            // `set_fuel` fails when fuel is not configured, so it is skipped for C/D.
            store.set_fuel(MAX_WASM_FUEL).map_err(|e| e.to_string())?;
        }
        let instance = linker
            .instantiate(&mut store, &self.module)
            .map_err(|e| e.to_string())?;
        let memory = instance
            .get_memory(&mut store, "memory")
            .ok_or("no memory export")?;
        let bump = instance
            .get_global(&mut store, "BUMP_PTR")
            .ok_or("no BUMP_PTR export")?;
        let input_len = u32::try_from(input.len()).map_err(|_| "input too long")?;
        let base_ptr = alloc_from_bump(&memory, &bump, &mut store, input_len)?;
        memory
            .write(&mut store, base_ptr as usize, input)
            .map_err(|e| e.to_string())?;
        let func = find_tool_main(&instance, &mut store).ok_or("no tool_main export")?;
        let ty = func.ty(&store);
        let params: Vec<Val> = ty
            .params()
            .enumerate()
            .map(|(i, param_ty)| {
                let val = if i == 0 {
                    i64::from(base_ptr)
                } else {
                    input.len() as i64
                };
                match param_ty {
                    ValType::I32 => Val::I32(val as i32),
                    _ => Val::I64(val),
                }
            })
            .collect();
        let mut results = vec![Val::I64(0); ty.results().len()];
        if let Err(e) = func.call(&mut store, &params, &mut results) {
            if store.data().fuel_exhausted {
                return Err("fuel exhausted".into());
            }
            return Err(format!("trapped: {e:#}"));
        }
        let fuel_consumed = fuel_budget - store.data().fuel_remaining;
        let packed = match results.first() {
            Some(Val::I64(v)) => *v,
            Some(Val::I32(v)) => i64::from(*v),
            _ => 0,
        };
        if packed < 0 {
            return Err(format!("tool returned error ({})", -packed));
        }
        let result_ptr = ((packed >> 32) as u32) as usize;
        let result_len = ((packed & 0xFFFF_FFFF) as u32) as usize;
        let mut output = vec![0u8; result_len];
        if result_len > 0 {
            memory
                .read(&store, result_ptr, &mut output)
                .map_err(|e| e.to_string())?;
        }
        Ok((output, fuel_consumed))
    }
}

fn alloc_from_bump(
    memory: &wasmtime::Memory,
    bump: &wasmtime::Global,
    store: &mut impl wasmtime::AsContextMut<Data = MirrorData>,
    size: u32,
) -> Result<u32, String> {
    let ptr = bump
        .get(&mut *store)
        .i32()
        .ok_or("BUMP_PTR is not an i32")? as u32;
    let new_ptr = ptr
        .checked_add(size)
        .ok_or_else(|| "guest allocation overflowed BUMP_PTR".to_owned())?;
    let current = memory.data_size(&mut *store) as u64;
    let required_end = u64::from(new_ptr);
    if required_end > current {
        let budget = store.as_context().data().memory_budget as u64;
        if required_end > budget {
            return Err("guest allocation exceeds forge memory limit".into());
        }
        let pages = (required_end - current).div_ceil(WASM_PAGE_SIZE);
        memory.grow(&mut *store, pages).map_err(|e| e.to_string())?;
    }
    bump.set(&mut *store, Val::I32(new_ptr as i32))
        .map_err(|e| e.to_string())?;
    Ok(ptr)
}

fn find_tool_main(
    instance: &wasmtime::Instance,
    store: &mut Store<MirrorData>,
) -> Option<wasmtime::Func> {
    if let Some(f) = instance.get_func(&mut *store, "tool__tool_main") {
        return Some(f);
    }
    for export in instance.exports(&mut *store) {
        if export.name().contains("tool_main")
            && let Some(f) = export.into_func()
        {
            return Some(f);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Conditions and sampling.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Condition {
    A,
    B,
    C,
    D,
    AMirror,
    BMirror,
}

const CONDITIONS: [Condition; 6] = [
    Condition::A,
    Condition::B,
    Condition::C,
    Condition::D,
    Condition::AMirror,
    Condition::BMirror,
];

impl Condition {
    fn label(self) -> &'static str {
        match self {
            Self::A => "A",
            Self::B => "B",
            Self::C => "C",
            Self::D => "D",
            Self::AMirror => "A'",
            Self::BMirror => "B'",
        }
    }

    fn module(self) -> &'static str {
        match self {
            Self::A | Self::D | Self::AMirror => "A0",
            Self::B | Self::C | Self::BMirror => "A1",
        }
    }

    fn path(self) -> &'static str {
        match self {
            Self::A | Self::B => "shipped execute_ephemeral",
            Self::C | Self::D => "mirror, wasmtime fuel off",
            Self::AMirror | Self::BMirror => "mirror, wasmtime fuel on",
        }
    }

    fn fuel_mode(self) -> &'static str {
        match self {
            Self::A | Self::AMirror => "host decrements + backstop",
            Self::B | Self::BMirror => "backstop only",
            Self::C => "none",
            Self::D => "host decrements only",
        }
    }
}

struct Executors {
    a0: Vec<u8>,
    a1: Vec<u8>,
    mirrors: [(Condition, Mirror); 4],
}

impl Executors {
    fn run(
        &self,
        condition: Condition,
        input: &[u8],
        fuel_budget: u64,
    ) -> Result<(Vec<u8>, u64), String> {
        match condition {
            Condition::A | Condition::B => {
                let bytes = if condition == Condition::A {
                    &self.a0
                } else {
                    &self.a1
                };
                execute_ephemeral(bytes, input, fuel_budget, &IoGrants::default())
                    .map(|r| (r.output, r.fuel_consumed))
                    .map_err(|e| e.to_string())
            }
            other => {
                let (_, mirror) = self
                    .mirrors
                    .iter()
                    .find(|(c, _)| *c == other)
                    .ok_or("mirror missing for condition")?;
                mirror.run(input, fuel_budget)
            }
        }
    }
}

struct BlockResult {
    condition: Condition,
    len: usize,
    warmup_ns: u128,
    fuel_consumed: u64,
    samples_ns: Vec<u128>,
}

impl BlockResult {
    fn sorted(&self) -> Vec<u128> {
        let mut s = self.samples_ns.clone();
        s.sort_unstable();
        s
    }
    fn median_ns(&self) -> u128 {
        percentile(&self.sorted(), 50.0)
    }
    fn p90_ns(&self) -> u128 {
        percentile(&self.sorted(), 90.0)
    }
    fn max_ns(&self) -> u128 {
        self.sorted().last().copied().unwrap_or(0)
    }
    fn min_ns(&self) -> u128 {
        self.sorted().first().copied().unwrap_or(0)
    }
    fn cv_pct(&self) -> f64 {
        cv_pct(&self.samples_ns)
    }
    fn flag(&self) -> &'static str {
        let cv = self.cv_pct();
        if cv < CV_CONVERGED {
            "✓"
        } else if cv < CV_DROP {
            "⚠"
        } else {
            "✗"
        }
    }
}

fn percentile(sorted: &[u128], pct: f64) -> u128 {
    if sorted.is_empty() {
        return 0;
    }
    let idx = ((sorted.len() as f64 - 1.0) * pct / 100.0).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn mean(samples: &[u128]) -> f64 {
    samples.iter().sum::<u128>() as f64 / samples.len() as f64
}

fn cv_pct(samples: &[u128]) -> f64 {
    if samples.len() < 2 {
        return 0.0;
    }
    let m = mean(samples);
    if m == 0.0 {
        return 0.0;
    }
    let var = samples
        .iter()
        .map(|&x| {
            let d = x as f64 - m;
            d * d
        })
        .sum::<f64>()
        / (samples.len() - 1) as f64;
    var.sqrt() / m * 100.0
}

fn us(ns: u128) -> f64 {
    ns as f64 / 1000.0
}

/// One timed call. Fails closed on anything but `Ok` with the expected bytes.
fn timed_call(
    executors: &Executors,
    condition: Condition,
    workload: &Workload,
    fuel_budget: u64,
) -> Result<(u128, u64), String> {
    let start = Instant::now();
    let outcome = executors.run(condition, &workload.input, fuel_budget);
    let elapsed = start.elapsed().as_nanos();
    let (output, fuel_consumed) = outcome.map_err(|e| {
        format!(
            "condition {} at L={} did not return Ok: {e}",
            condition.label(),
            workload.len
        )
    })?;
    if output != workload.expected {
        return Err(format!(
            "condition {} at L={} returned {:?}, expected {:?}",
            condition.label(),
            workload.len,
            String::from_utf8_lossy(&output),
            String::from_utf8_lossy(&workload.expected)
        ));
    }
    Ok((elapsed, fuel_consumed))
}

fn measure_block(
    executors: &Executors,
    condition: Condition,
    workload: &Workload,
    fuel_budget: u64,
    max_samples: usize,
) -> Result<BlockResult, String> {
    let mut warmup_ns = 0;
    for _ in 0..WARMUP_RUNS {
        warmup_ns = timed_call(executors, condition, workload, fuel_budget)?.0;
    }
    let mut samples_ns = Vec::with_capacity(MIN_SAMPLES);
    let mut fuel_consumed = 0;
    while samples_ns.len() < max_samples {
        let (ns, fuel) = timed_call(executors, condition, workload, fuel_budget)?;
        samples_ns.push(ns);
        fuel_consumed = fuel;
        if samples_ns.len() >= MIN_SAMPLES {
            let trailing = &samples_ns[samples_ns.len() - MIN_SAMPLES..];
            if cv_pct(trailing) < CV_CONVERGED {
                break;
            }
        }
    }
    Ok(BlockResult {
        condition,
        len: workload.len,
        warmup_ns,
        fuel_consumed,
        samples_ns,
    })
}

// ---------------------------------------------------------------------------
// Driver.
// ---------------------------------------------------------------------------

fn tool_source_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("tools")
        .join("task098_levenshtein_distance.sigil")
}

fn run() -> Result<(), String> {
    let args = parse_args()?;
    if cfg!(debug_assertions) && !args.allow_debug {
        // Fail closed: a debug-profile number is not the number PERFORMANCE.md publishes.
        return Err("built without --release; pass --allow-debug for a smoke run".into());
    }
    fs::create_dir_all(&args.out).map_err(|e| format!("create {}: {e}", args.out.display()))?;
    let started = Instant::now();

    // Workload.
    let source_path = tool_source_path();
    let source_bytes =
        fs::read(&source_path).map_err(|e| format!("read {}: {e}", source_path.display()))?;
    let source_sha256 = sha256_hex(&source_bytes);
    let source = String::from_utf8(source_bytes).map_err(|e| e.to_string())?;
    let a0 = build_a0(&source)?;
    let a1 = build_a1(&a0.bytes)?;
    fs::write(args.out.join("a0.wasm"), &a0.bytes).map_err(|e| e.to_string())?;
    fs::write(args.out.join("a1.wasm"), &a1.bytes).map_err(|e| e.to_string())?;

    let mut rng = SplitMix64(args.seed);
    let mut workloads: Vec<Workload> = args
        .lengths
        .iter()
        .map(|&len| make_workload(&mut rng, len))
        .collect();
    workloads.sort_by_key(|w| w.len);
    for w in &workloads {
        fs::write(args.out.join(format!("input_L{}.txt", w.len)), &w.input)
            .map_err(|e| e.to_string())?;
    }

    // Executors: the two shipped conditions share the runtime's one-entry
    // module cache; the four mirrors are compiled once each, up front.
    let executors = Executors {
        mirrors: [
            (Condition::C, Mirror::new(&a1.bytes, false)?),
            (Condition::D, Mirror::new(&a0.bytes, false)?),
            (Condition::AMirror, Mirror::new(&a0.bytes, true)?),
            (Condition::BMirror, Mirror::new(&a1.bytes, true)?),
        ],
        a0: a0.bytes.clone(),
        a1: a1.bytes.clone(),
    };

    // Sanity: the known pair, through the shipped path, on both modules.
    let kitten = Workload {
        len: 6,
        input: b"kitten\nsitting".to_vec(),
        input_sha256: sha256_hex(b"kitten\nsitting"),
        expected: b"3".to_vec(),
    };
    for condition in CONDITIONS {
        timed_call(&executors, condition, &kitten, CALIBRATION_BUDGET)?;
    }

    // Calibration: fuel consumed by A per L, budget = 2x; every condition must
    // return Ok with identical output on every workload before any timing.
    let mut budgets = Vec::with_capacity(workloads.len());
    let mut calibrated = Vec::with_capacity(workloads.len());
    for w in &workloads {
        let (_, consumed) = timed_call(&executors, Condition::A, w, CALIBRATION_BUDGET)?;
        let budget = consumed
            .checked_mul(2)
            .ok_or("fuel budget overflow")?
            .max(1);
        for condition in CONDITIONS {
            timed_call(&executors, condition, w, budget)?;
        }
        budgets.push(budget);
        calibrated.push(consumed);
    }

    // Cold first calls through the shipped path: alternating modules defeats
    // the one-entry cache, so each call includes Wasmtime compilation.
    let l0 = workloads
        .iter()
        .find(|w| w.len == 0)
        .ok_or("L=0 workload missing")?;
    let l0_budget = budgets[workloads.iter().position(|w| w.len == 0).unwrap_or(0)];
    let mut cold: Vec<(Condition, u128)> = Vec::new();
    for _ in 0..args.cold_repeats {
        for condition in [Condition::A, Condition::B] {
            let (ns, _) = timed_call(&executors, condition, l0, l0_budget)?;
            cold.push((condition, ns));
        }
    }
    let mut mirror_compile: Vec<(&'static str, bool, u128)> = Vec::new();
    for _ in 0..args.cold_repeats {
        for (label, bytes) in [("A0", &a0.bytes), ("A1", &a1.bytes)] {
            for fuel_on in [true, false] {
                let start = Instant::now();
                let _ = Mirror::new(bytes, fuel_on)?;
                mirror_compile.push((label, fuel_on, start.elapsed().as_nanos()));
            }
        }
    }

    // Blocks in randomized order; never alternate modules inside a block.
    let mut blocks: Vec<(Condition, usize)> = Vec::new();
    for (i, _) in workloads.iter().enumerate() {
        for condition in CONDITIONS {
            blocks.push((condition, i));
        }
    }
    rng.shuffle(&mut blocks);
    let mut results: Vec<BlockResult> = Vec::with_capacity(blocks.len());
    for (k, &(condition, i)) in blocks.iter().enumerate() {
        let w = &workloads[i];
        eprintln!(
            "block {}/{}: {} L={}",
            k + 1,
            blocks.len(),
            condition.label(),
            w.len
        );
        results.push(measure_block(
            &executors,
            condition,
            w,
            budgets[i],
            args.max_samples,
        )?);
    }

    // Raw samples.
    let mut tsv = String::new();
    tsv.push_str(
        "# fuel_overhead raw samples: one row per block, samples in nanoseconds, in run order\n",
    );
    let _ = writeln!(
        tsv,
        "# seed={} (0x{:016x}) lengths={:?} max_samples={} tool_sha256={source_sha256}",
        args.seed, args.seed, args.lengths, args.max_samples
    );
    tsv.push_str("block\tcondition\tmodule\tpath\tL\tn\twarmup_ns\tfuel_consumed\tsamples_ns\n");
    for (k, r) in results.iter().enumerate() {
        let samples: Vec<String> = r.samples_ns.iter().map(u128::to_string).collect();
        let _ = writeln!(
            tsv,
            "{k}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            r.condition.label(),
            r.condition.module(),
            r.condition.path(),
            r.len,
            r.samples_ns.len(),
            r.warmup_ns,
            r.fuel_consumed,
            samples.join(" ")
        );
    }
    fs::write(args.out.join("samples.tsv"), tsv).map_err(|e| e.to_string())?;

    // Summary.
    let summary = Summary {
        args: &args,
        source_path: &source_path,
        source_sha256: &source_sha256,
        a0: &a0,
        a1: &a1,
        workloads: &workloads,
        budgets: &budgets,
        calibrated: &calibrated,
        cold: &cold,
        mirror_compile: &mirror_compile,
        results: &results,
        blocks: &blocks,
        elapsed_s: started.elapsed().as_secs(),
    }
    .render();
    fs::write(args.out.join("summary.md"), &summary).map_err(|e| e.to_string())?;
    print!("{summary}");
    Ok(())
}

struct Summary<'a> {
    args: &'a Args,
    source_path: &'a Path,
    source_sha256: &'a str,
    a0: &'a A0,
    a1: &'a A1,
    workloads: &'a [Workload],
    budgets: &'a [u64],
    calibrated: &'a [u64],
    cold: &'a [(Condition, u128)],
    mirror_compile: &'a [(&'static str, bool, u128)],
    results: &'a [BlockResult],
    blocks: &'a [(Condition, usize)],
    elapsed_s: u64,
}

impl Summary<'_> {
    fn result(&self, condition: Condition, len: usize) -> Option<&BlockResult> {
        self.results
            .iter()
            .find(|r| r.condition == condition && r.len == len)
    }

    /// The derived table for one per-block statistic (median or minimum).
    ///
    /// Every difference and ratio is taken on NET values (a condition's statistic
    /// minus that same condition's L=0 statistic). The shipped path registers 23
    /// host closures per call in a `--no-default-features` build — the 9 `sigil.*`
    /// imports plus the 14 `ffi.*` shims of `link_ffi_imports`; `--features solver`
    /// adds `ffi.z3_check` for 24 — whether or not the module imports them (counted
    /// as `.func_wrap(` call sites in `ephemeral.rs`); the module under test imports
    /// only `sigil.*`, so the mirror wraps two and traps the rest, and the two paths'
    /// fixed costs differ. Netting each
    /// condition against its own L=0 cancels that before A (shipped) is compared
    /// with C (mirror). A'/A and B'/B are the mirror's agreement with the shipped
    /// path, also on net values (the L=0 row has no net quantity and shows `—`).
    fn derived(
        &self,
        s: &mut String,
        plural: &str,
        singular: &str,
        stat: fn(&BlockResult) -> u128,
    ) {
        let _ = writeln!(
            s,
            "## Derived on {plural}, per L (net: each condition minus its own L=0 {singular})\n"
        );
        s.push_str("| L | A (µs) | B (µs) | C (µs) | D (µs) | A/C | B/C | D/C | (A−B)/L² ns | (B−C)/L² ns | (A−B)/fuel ns | A'/A | B'/B |\n");
        s.push_str("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n");
        let value = |c: Condition, len: usize| -> f64 {
            self.result(c, len)
                .map(|r| stat(r) as f64)
                .unwrap_or(f64::NAN)
        };
        for w in self.workloads {
            let l = w.len;
            let a = value(Condition::A, l);
            let b = value(Condition::B, l);
            let c = value(Condition::C, l);
            let d = value(Condition::D, l);
            let am = value(Condition::AMirror, l);
            let bm = value(Condition::BMirror, l);
            let a_net = a - value(Condition::A, 0);
            let b_net = b - value(Condition::B, 0);
            let c_net = c - value(Condition::C, 0);
            let d_net = d - value(Condition::D, 0);
            let am_net = am - value(Condition::AMirror, 0);
            let bm_net = bm - value(Condition::BMirror, 0);
            let cells = (l * l) as f64;
            let fuel = self
                .result(Condition::A, l)
                .map(|r| r.fuel_consumed as f64)
                .unwrap_or(f64::NAN);
            // L=0 has no net quantity to divide by; the row shows raw values only.
            let over = |num: f64, den: f64| -> String {
                if l == 0 || den <= 0.0 {
                    "—".to_owned()
                } else {
                    format!("{:.2}", num / den)
                }
            };
            let over3 = |num: f64, den: f64| -> String {
                if l == 0 || den <= 0.0 {
                    "—".to_owned()
                } else {
                    format!("{:.3}", num / den)
                }
            };
            let _ = writeln!(
                s,
                "| {l} | {:.1} | {:.1} | {:.1} | {:.1} | {} | {} | {} | {} | {} | {} | {} | {} |",
                a / 1000.0,
                b / 1000.0,
                c / 1000.0,
                d / 1000.0,
                over(a_net, c_net),
                over(b_net, c_net),
                over(d_net, c_net),
                over(a_net - b_net, cells),
                over(b_net - c_net, cells),
                over(a_net - b_net, fuel),
                over3(am_net, a_net),
                over3(bm_net, b_net)
            );
        }
        s.push('\n');
    }

    fn render(&self) -> String {
        let mut s = String::new();
        s.push_str("# Fuel-instrumentation runtime overhead — task098 Levenshtein\n\n");
        let _ = writeln!(
            s,
            "Harness `crates/sigil-runtime/examples/fuel_overhead.rs`; profile {}; seed {} (0x{:016x}); \
             lengths {:?}; convergence trailing-{MIN_SAMPLES} CV < {CV_CONVERGED:.0}% or {} samples; \
             {WARMUP_RUNS} warm-up per block discarded; wall time {} s.",
            if cfg!(debug_assertions) {
                "DEBUG (not publishable)"
            } else {
                "release"
            },
            self.args.seed,
            self.args.seed,
            self.args.lengths,
            self.args.max_samples,
            self.elapsed_s
        );
        s.push('\n');

        s.push_str("## Workload\n\n");
        let _ = writeln!(
            s,
            "- Tool: `{}` (sha256 `{}`)",
            self.source_path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("?"),
            self.source_sha256
        );
        s.push_str("- Sanity: `kitten\\nsitting` returned `3` on every condition.\n");
        s.push_str("- Inputs (two `[a-z]` strings of length L joined by one `\\n`; L=0 is the bare `\\n`):\n\n");
        s.push_str(
            "| L | input bytes | sha256 | expected output | fuel consumed (A) | budget passed |\n",
        );
        s.push_str("|---:|---:|---|---:|---:|---:|\n");
        for (i, w) in self.workloads.iter().enumerate() {
            let _ = writeln!(
                s,
                "| {} | {} | `{}` | {} | {} | {} |",
                w.len,
                w.input.len(),
                w.input_sha256,
                String::from_utf8_lossy(&w.expected),
                self.calibrated[i],
                self.budgets[i]
            );
        }
        s.push('\n');

        s.push_str("## Modules\n\n");
        let _ = writeln!(
            s,
            "- A0: {} bytes, sha256 `{}`, {} functions, compiler static fuel budget {}; imports: {}.",
            self.a0.bytes.len(),
            sha256_hex(&self.a0.bytes),
            self.a0.function_count,
            self.a0.static_fuel_budget,
            self.a0.imports.join(", ")
        );
        let _ = writeln!(
            s,
            "- A1: {} bytes, sha256 `{}`; {} `call 0` sites replaced by `drop` across {} function bodies; \
             {} non-code sections copied byte-for-byte (digests equal); validates; zero `call 0` remain.",
            self.a1.bytes.len(),
            sha256_hex(&self.a1.bytes),
            self.a1.replaced_calls,
            self.a1.functions,
            self.a1.sections_copied
        );
        s.push('\n');

        s.push_str("## Cold first call (shipped path, includes Wasmtime compilation)\n\n");
        s.push_str("| call | condition | µs |\n|---:|---|---:|\n");
        for (k, (condition, ns)) in self.cold.iter().enumerate() {
            let _ = writeln!(s, "| {} | {} | {:.1} |", k + 1, condition.label(), us(*ns));
        }
        s.push_str("\nMirror `Module::from_binary` alone:\n\n| module | wasmtime fuel | µs |\n|---|---|---:|\n");
        for (label, fuel_on, ns) in self.mirror_compile {
            let _ = writeln!(
                s,
                "| {label} | {} | {:.1} |",
                if *fuel_on { "on" } else { "off" },
                us(*ns)
            );
        }
        s.push('\n');

        s.push_str("## Per-block results\n\n");
        s.push_str("| Condition | Module | Path | Fuel | L | n | Warm-up (µs) | Min (µs) | Median (µs) | P90 (µs) | Max (µs) | CV % | Flag | fuel_consumed |\n");
        s.push_str("|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|:-:|---:|\n");
        for w in self.workloads {
            for condition in CONDITIONS {
                if let Some(r) = self.result(condition, w.len) {
                    let _ = writeln!(
                        s,
                        "| {} | {} | {} | {} | {} | {} | {:.1} | {:.1} | {:.1} | {:.1} | {:.1} | {:.1} | {} | {} |",
                        condition.label(),
                        condition.module(),
                        condition.path(),
                        condition.fuel_mode(),
                        r.len,
                        r.samples_ns.len(),
                        us(r.warmup_ns),
                        us(r.min_ns()),
                        us(r.median_ns()),
                        us(r.p90_ns()),
                        us(r.max_ns()),
                        r.cv_pct(),
                        r.flag(),
                        r.fuel_consumed
                    );
                }
            }
        }
        s.push('\n');

        self.derived(&mut s, "medians", "median", BlockResult::median_ns);
        self.derived(&mut s, "minima", "minimum", BlockResult::min_ns);

        s.push_str("## Block order\n\n");
        let order: Vec<String> = self
            .blocks
            .iter()
            .map(|(c, i)| format!("{}:L{}", c.label(), self.workloads[*i].len))
            .collect();
        let _ = writeln!(s, "{}", order.join(", "));
        s
    }
}
