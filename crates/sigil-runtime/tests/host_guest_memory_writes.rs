//! Every host write into GUEST linear memory lands in a FRESH bump-pointer cell.
//!
//! This is the premise the taint checker's S1 heap floor rests on
//! (`crates/sigil-compiler/src/taint_check.rs`, `HEAP_FLOOR_AFTER_FFI`): after an
//! FFI call only the RAW-load floor rises, because whatever the host wrote sits
//! in cells `alloc_from_bump` handed out at or above `BUMP_PTR` — cells no live
//! typed value overlaps — so a typed read (`a[i]`, `r.f`) cannot observe host
//! bytes. That is a property of THIS repo's hosts, not an axiom, and a premise
//! nobody measures is a hope (`docs/RESIDUAL_RISKS.md` SR-024): a future shim
//! that writes at a CALLER-SUPPLIED address would let a typed read see host
//! bytes at a clean floor, and S1 would be too weak without anyone noticing.
//!
//! So the premise is a census. Every site under `crates/*/src` that can write
//! guest memory — wasmtime's `Memory::write(&mut store, ptr, bytes)`, the
//! writable view `Memory::data_mut(&mut store)`, and the raw pointer
//! `Memory::data_ptr(..)` — is located, attributed to its enclosing function,
//! and required to bind its destination through `alloc_from_bump` earlier in
//! that function. The expected site list is pinned EXACTLY (SC-P1), so a new
//! write site fails here by name and must either take its destination from the
//! bump allocator or make S1 floor typed reads too. `Store::data_mut()` — the
//! host's own per-execution data, not guest memory — takes no argument, which is
//! what keeps it out of the census.
//!
//! FAILURE DIRECTION: a shape the detector does not recognize is a MISSED write
//! site, so the anti-stub plants each recognized shape and the census asserts
//! the real sites are found (a census that saw zero sites would be vacuous and
//! fails). What this file does not cover: a host writing guest memory through a
//! path that is not one of the three wasmtime entry points above — none exists
//! in the workspace today, and adding one is exactly the kind of change that
//! must extend `WRITE_SHAPES` first.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("sigil-runtime must be under crates/")
        .to_path_buf()
}

/// The source shapes through which a host can write guest linear memory. The
/// `(&` after `data_mut` is load-bearing: `Memory::data_mut(&mut store)` takes
/// the store as an argument, `Store::data_mut()` (host data, not guest memory)
/// takes none.
const WRITE_SHAPES: &[&str] = &[".write(&mut", "Memory::write(", ".data_mut(&", ".data_ptr("];

/// One guest-memory write site, attributed to its enclosing function.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct WriteSite {
    file: String,
    function: String,
    /// Whether the enclosing function binds a pointer through `alloc_from_bump`
    /// BEFORE the write — the fresh-cell premise, checked per site.
    destination_is_fresh: bool,
}

/// The name of the `fn` item a line at `index` sits in: the nearest preceding
/// line that begins a function item. `None` when there is none (a write at
/// module level — impossible in Rust, but reported rather than dropped).
fn enclosing_fn(lines: &[&str], index: usize) -> Option<(usize, String)> {
    (0..index).rev().find_map(|j| {
        let t = lines[j].trim_start();
        let rest = t
            .strip_prefix("pub(crate) fn ")
            .or_else(|| t.strip_prefix("pub fn "))
            .or_else(|| t.strip_prefix("fn "))?;
        let name: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
            .collect();
        (!name.is_empty()).then_some((j, name))
    })
}

/// Every guest-memory write site in one source file. Comment lines are skipped
/// (a shape mentioned in prose is not a write); everything else that contains
/// a shape is a site.
fn guest_write_sites(rel: &str, src: &str) -> Vec<WriteSite> {
    let lines: Vec<&str> = src.lines().collect();
    let mut out = Vec::new();
    for (i, line) in lines.iter().enumerate() {
        let t = line.trim_start();
        if t.starts_with("//") || !WRITE_SHAPES.iter().any(|shape| line.contains(shape)) {
            continue;
        }
        let (function, destination_is_fresh) = match enclosing_fn(&lines, i) {
            Some((start, name)) => {
                let fresh = lines[start..i]
                    .iter()
                    .any(|l| !l.trim_start().starts_with("//") && l.contains("alloc_from_bump("));
                (name, fresh)
            }
            None => ("<no enclosing fn>".to_owned(), false),
        };
        out.push(WriteSite {
            file: rel.to_owned(),
            function,
            destination_is_fresh,
        });
    }
    out
}

/// Every `.rs` file under `crates/*/src`, workspace-relative with forward
/// slashes (stable across hosts).
fn src_files() -> Vec<(String, String)> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<(String, String)>) {
        let entries = std::fs::read_dir(dir)
            .unwrap_or_else(|err| panic!("cannot read {}: {err}", dir.display()));
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(&path, root, out);
            } else if path.extension().is_some_and(|ext| ext == "rs") {
                let rel = path
                    .strip_prefix(root)
                    .expect("walked path is under the workspace root")
                    .to_string_lossy()
                    .replace('\\', "/");
                let src = std::fs::read_to_string(&path)
                    .unwrap_or_else(|err| panic!("cannot read {}: {err}", path.display()));
                out.push((rel, src));
            }
        }
    }
    let root = workspace_root();
    let mut out = Vec::new();
    let crates = root.join("crates");
    for entry in std::fs::read_dir(&crates)
        .expect("crates/ exists")
        .flatten()
    {
        let src = entry.path().join("src");
        if src.is_dir() {
            walk(&src, &root, &mut out);
        }
    }
    out.sort();
    out
}

/// The pinned census: exactly the two ephemeral-host writes — the shared
/// `write_to_guest` every byte-returning shim uses, and the tool-input write in
/// `execute_ephemeral_inner` — both with a bump-allocated destination. The actor
/// host writes guest memory nowhere. Measured at introduction (SC-P1).
#[test]
fn every_host_write_into_guest_memory_lands_in_a_fresh_bump_cell() {
    let sites: BTreeSet<WriteSite> = src_files()
        .iter()
        .flat_map(|(rel, src)| guest_write_sites(rel, src))
        .collect();
    let expected: BTreeSet<WriteSite> =
        [("execute_ephemeral_inner", true), ("write_to_guest", true)]
            .into_iter()
            .map(|(function, destination_is_fresh)| WriteSite {
                file: "crates/sigil-runtime/src/ephemeral.rs".to_owned(),
                function: function.to_owned(),
                destination_is_fresh,
            })
            .collect();
    assert!(
        !sites.is_empty(),
        "the census saw no guest-memory write at all: the detector is broken, not the hosts clean"
    );
    assert_eq!(
        sites, expected,
        "the set of host writes into guest memory moved. A NEW site must take its destination \
         from `alloc_from_bump` (then extend this pin), or S1 in taint_check.rs must start \
         flooring typed reads after FFI — see docs/RESIDUAL_RISKS.md SR-024"
    );
    assert!(
        sites.iter().all(|site| site.destination_is_fresh),
        "a host write whose destination is not bump-allocated breaks the S1 premise: {sites:?}"
    );
}

/// SC-P4 anti-stub: the detector reports a planted write at a caller-supplied
/// address (no `alloc_from_bump` in scope), recognizes each write shape, skips a
/// shape mentioned only in a comment, and does NOT mistake the host's own
/// `Store::data_mut()` for a guest-memory write.
#[test]
fn guest_memory_write_census_detects_a_planted_caller_supplied_address() {
    let planted = "\
fn evil(memory: &wasmtime::Memory, store: &mut S, ptr: u32, data: &[u8]) {
    // memory.write(&mut store, 0, data) — prose, not a site
    memory.write(&mut *store, ptr as usize, data).unwrap();
}
pub fn view(memory: &wasmtime::Memory, store: &mut S) -> &mut [u8] {
    memory.data_mut(&mut *store)
}
pub(crate) fn raw(memory: &wasmtime::Memory, store: &S) -> *mut u8 {
    memory.data_ptr(store)
}
fn host_only(caller: &mut Caller<'_, D>) {
    caller.data_mut().fuel = 0;
}
fn fresh(memory: &wasmtime::Memory, store: &mut S, data: &[u8]) {
    let ptr = alloc_from_bump(memory, store, data.len());
    memory.write(&mut *store, ptr as usize, data).unwrap();
}
";
    let found = guest_write_sites("planted.rs", planted);
    let site = |function: &str, destination_is_fresh: bool| WriteSite {
        file: "planted.rs".to_owned(),
        function: function.to_owned(),
        destination_is_fresh,
    };
    assert_eq!(
        found,
        vec![
            site("evil", false),
            site("view", false),
            site("raw", false),
            site("fresh", true),
        ],
        "the detector must report the caller-supplied-address write, both view shapes, and the \
         fresh write, and must ignore the comment and the host's own Store::data_mut()"
    );
}
