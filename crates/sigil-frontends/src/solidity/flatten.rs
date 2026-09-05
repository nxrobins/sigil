//! SOL-INH: reduce a parsed file's `Vec<Contract>` to the single synthetic `Contract` the rest
//! of the pipeline (`validate_user_identifiers → desugar → check → emit`) consumes unchanged.
//!
//! **M1: C3 linearization + per-member merge.** A multi-contract file with a `contract X is A, B`
//! hierarchy is flattened into ONE contract whose members are the C3-merged union of the whole
//! transitive base DAG — overrides resolved derived-wins, inherited modifiers carried with their
//! bodies, state laid out most-base-first. The downstream pipeline never changes: flatten always
//! hands it one `Contract` indistinguishable from a hand-written flat one.
//!
//! **The existential** (a security translator): a flatten that COMPILES but is WEAKER/different
//! than the source — a silently dropped inherited modifier (`onlyOwner` vanishes), a mis-resolved
//! override (base body wins over derived), a wrong C3 order, or a lost state field. Every step
//! fails CLOSED: reject what we can't faithfully flatten, never emit a plausible-but-wrong one.
//!
//! **Scope (fail-closed; each rejects the WHOLE translation):** concrete + abstract bases merge
//! (SOL-XFILE PR2), interface bases contribute nothing, a `library` base → FE476; a base named in
//! `is` not resolved (this file / the project union) → FE476; a base (non-main) `constructor` is
//! DROPPED iff metadata-only, and the deployed ctor's base-calls are reduced iff all-literal to a
//! metadata base — otherwise FE468 (SOL-XFILE PR4/L3); `super`/internal calls are FE401 downstream.
//! The byte-identical single-concrete-no-bases path is preserved (EX-9).

use super::parser::{
    AssignOp, Constructor, Contract, ContractKind, Enum, Expr, Function, Modifier, ParsedFile,
    Program, StateVar, Stmt, Struct, TypeRef,
};
use crate::FrontendDiag;
use crate::codes;
use crate::limits::MAX_FUNCTIONS;
use std::collections::{HashMap, HashSet};
use std::ops::Range;

/// SOL-INH totality bounds (EX-8 — checked BEFORE the merged AST is built, all → FE402).
const MAX_CONTRACTS: usize = 64; // top-level contracts per file
const MAX_INH_DEPTH: u32 = 16; // inheritance recursion depth (bounds the native stack in C3)
const MAX_LINEARIZED: usize = 32; // C3 linearization length

/// Reduce a `ParsedFile` to a `Program` (pragma + the single flattened contract to translate).
pub fn flatten(parsed: ParsedFile) -> Result<Program, FrontendDiag> {
    let ParsedFile {
        pragma, contracts, ..
    } = parsed;

    // EX-9 fast path: a lone flat concrete contract reduces by MOVE, untouched (byte-identical).
    if contracts.len() == 1
        && contracts[0].kind == ContractKind::Concrete
        && contracts[0].bases.is_empty()
    {
        let contract = contracts.into_iter().next().expect("len == 1");
        return Ok(Program { pragma, contract });
    }

    // Totality: the parser already bounds the count, but re-check at the flatten entry (defensive).
    if contracts.len() > MAX_CONTRACTS {
        return Err(diag(
            codes::FE402_TOO_LARGE_SOL,
            format!("too many top-level contracts (max {MAX_CONTRACTS})"),
            0..0,
        ));
    }
    if contracts.is_empty() {
        return Err(diag(
            codes::FE470_AMBIGUOUS_MAIN_SOL,
            "no contract to translate in this file",
            0..0,
        ));
    }

    // Index contracts by name; a duplicate top-level name is a Solidity declaration conflict.
    let mut by_name: HashMap<&str, usize> = HashMap::new();
    for (i, c) in contracts.iter().enumerate() {
        if by_name.insert(c.name.as_str(), i).is_some() {
            return Err(diag(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!("duplicate top-level contract name `{}`", c.name),
                c.span.clone(),
            ));
        }
    }

    let main_idx = select_main(&contracts)?;
    // C3-linearize the main over the TRANSITIVE base DAG — most-derived-first.
    let lin = Linearizer::new(&contracts, &by_name).run(main_idx)?;
    let contract = merge(&contracts, main_idx, &lin)?;
    Ok(Program { pragma, contract })
}

/// SOL-XFILE PR1 — flatten a PROJECT UNION with the main PINNED to `entry_main` (the
/// ENTRY-MAIN RULE, EX-1): the translated contract is ALWAYS the entry file's concrete
/// contract, NEVER a union-wide sink inference — an imported file's unrelated (or
/// entry-deriving) concrete contract can neither flip FE470 nor steal main (MC-1). The
/// duplicate-name gate, C3 linearization, and per-member merge are the SAME code paths
/// as single-file `flatten` (which stays byte-identical — this is a parallel entry, not
/// a change). `entry_main` is resolved by `project.rs` from the entry file BEFORE the
/// union, so a lookup miss here is an internal invariant break (FE500), never user error.
pub fn flatten_project(parsed: ParsedFile, entry_main: &str) -> Result<Program, FrontendDiag> {
    let ParsedFile {
        pragma, contracts, ..
    } = parsed;

    // Totality at the UNION level: the per-file parser bounds each file's count, but the
    // union across a closure can exceed it — same dumb cap, checked before any work.
    if contracts.len() > MAX_CONTRACTS {
        return Err(diag(
            codes::FE402_TOO_LARGE_SOL,
            format!("too many contracts across the project closure (max {MAX_CONTRACTS})"),
            0..0,
        ));
    }

    // Index by name; a duplicate across ANY two closure files is a hard reject (never a
    // silent shadowing / wrong-symbol resolution — the union keeps names globally unique).
    let mut by_name: HashMap<&str, usize> = HashMap::new();
    for (i, c) in contracts.iter().enumerate() {
        if by_name.insert(c.name.as_str(), i).is_some() {
            return Err(diag(
                codes::FE420_BAD_IDENTIFIER_SOL,
                format!(
                    "duplicate top-level contract name `{}` across the project",
                    c.name
                ),
                c.span.clone(),
            ));
        }
    }

    let Some(&main_idx) = by_name.get(entry_main) else {
        return Err(diag(
            codes::FE500_INTERNAL_MALFORMED,
            format!("internal: entry main `{entry_main}` vanished from the project union"),
            0..0,
        ));
    };
    let lin = Linearizer::new(&contracts, &by_name).run(main_idx)?;
    let contract = merge(&contracts, main_idx, &lin)?;
    Ok(Program { pragma, contract })
}

/// The deployable contract = the UNIQUE concrete sink (a concrete contract nobody inherits from).
/// Interface/library/abstract declarations are excluded as candidates (they're never deployed),
/// though they can be bases. Zero concrete sinks → a cycle (FE469) or no concrete at all (FE470);
/// ≥2 → ambiguous (FE470 — v1 translates one deployable per file, no `--contract` selector).
fn select_main(contracts: &[Contract]) -> Result<usize, FrontendDiag> {
    // A contract is "inherited" (not a deployable sink) only when a CONCRETE contract derives from
    // it — an abstract/interface INHERITOR is itself undeployable, so it must NOT mask the concrete
    // it extends (e.g. `contract Token {} abstract Extension is Token {}` deploys Token, not error).
    // SOL-XFILE PR2 admits abstract/interface BASES, but the sink set is still exactly the concrete
    // contracts that no concrete contract derives from: abstract/interface contracts are excluded
    // as candidates by the `kind == Concrete` filter, so only concrete→X edges can hide a sink, and
    // scanning concrete contracts' direct bases captures every such edge. (In project mode the
    // entry-main rule pins main directly and this fn is unused — it governs the single-file path.)
    let mut inherited: HashSet<&str> = HashSet::new();
    for c in contracts {
        if c.kind != ContractKind::Concrete {
            continue;
        }
        for b in &c.bases {
            inherited.insert(b.name.as_str());
        }
    }
    let sinks: Vec<usize> = contracts
        .iter()
        .enumerate()
        .filter(|(_, c)| c.kind == ContractKind::Concrete && !inherited.contains(c.name.as_str()))
        .map(|(i, _)| i)
        .collect();
    match sinks.len() {
        1 => Ok(sinks[0]),
        0 => {
            let has_concrete = contracts.iter().any(|c| c.kind == ContractKind::Concrete);
            if has_concrete {
                // Every concrete contract is inherited by another → a cycle among concretes.
                Err(diag(
                    codes::FE469_INHERITANCE_CYCLE_SOL,
                    "inheritance cycle — no concrete contract is a sink (one would deploy)",
                    contracts[0].span.clone(),
                ))
            } else {
                Err(diag(
                    codes::FE470_AMBIGUOUS_MAIN_SOL,
                    "no concrete contract to translate (only interfaces/libraries/abstracts)",
                    contracts[0].span.clone(),
                ))
            }
        }
        _ => {
            let names: Vec<&str> = sinks.iter().map(|&i| contracts[i].name.as_str()).collect();
            Err(diag(
                codes::FE470_AMBIGUOUS_MAIN_SOL,
                format!(
                    "ambiguous main: {} independent deployable contracts ({}) — v1 translates one per file",
                    sinks.len(),
                    names.join(", "),
                ),
                contracts[sinks[1]].span.clone(),
            ))
        }
    }
}

/// C3 linearization (the exact solc MRO). `L[C] = [C] ++ merge(L[B_k], …, L[B_1], [B_k, …, B_1])`
/// — direct bases taken RIGHT-TO-LEFT (solc lists them most-base-like to most-derived, so the
/// last-listed base is the most derived), result MOST-DERIVED-FIRST. Memoized per contract;
/// recursion bounded by `MAX_INH_DEPTH` (the native-stack guard) and the result by `MAX_LINEARIZED`.
struct Linearizer<'a> {
    contracts: &'a [Contract],
    by_name: &'a HashMap<&'a str, usize>,
    memo: HashMap<usize, Vec<usize>>,
    on_stack: HashSet<usize>,
}

impl<'a> Linearizer<'a> {
    fn new(contracts: &'a [Contract], by_name: &'a HashMap<&'a str, usize>) -> Self {
        Linearizer {
            contracts,
            by_name,
            memo: HashMap::new(),
            on_stack: HashSet::new(),
        }
    }

    fn run(mut self, start: usize) -> Result<Vec<usize>, FrontendDiag> {
        self.lin(start, 0)
    }

    fn lin(&mut self, i: usize, depth: u32) -> Result<Vec<usize>, FrontendDiag> {
        if depth > MAX_INH_DEPTH {
            return Err(diag(
                codes::FE402_TOO_LARGE_SOL,
                format!("inheritance depth exceeds {MAX_INH_DEPTH}"),
                self.contracts[i].span.clone(),
            ));
        }
        if let Some(l) = self.memo.get(&i) {
            return Ok(l.clone());
        }
        if !self.on_stack.insert(i) {
            return Err(diag(
                codes::FE469_INHERITANCE_CYCLE_SOL,
                format!("inheritance cycle through `{}`", self.contracts[i].name),
                self.contracts[i].span.clone(),
            ));
        }

        // Resolve direct bases RIGHT-TO-LEFT into their linearizations + the direct-base list.
        let mut lists: Vec<Vec<usize>> = Vec::new();
        let mut direct_rev: Vec<usize> = Vec::new();
        for b in self.contracts[i].bases.iter().rev() {
            let &bi = self.by_name.get(b.name.as_str()).ok_or_else(|| {
                diag(
                    codes::FE476_IMPORT_OR_BASE_SOL,
                    format!(
                        "base contract `{}` is not defined in this file (cross-file imports are not resolved)",
                        b.name
                    ),
                    b.span.clone(),
                )
            })?;
            // SOL-XFILE PR2/L2: an ABSTRACT base merges like a concrete (its parsed members are
            // the inherited implementation); an INTERFACE base linearizes but contributes ZERO
            // members (its body was parse-skipped — there is nothing to merge, and solc already
            // verified conformance); a LIBRARY base is out of the subset (libraries are
            // `using`-attached / called, never a faithful inheritance base here) → FE476.
            if self.contracts[bi].kind == ContractKind::Library {
                return Err(diag(
                    codes::FE476_IMPORT_OR_BASE_SOL,
                    format!(
                        "base contract `{}` is a library — a library is not an inheritance base in the subset",
                        b.name
                    ),
                    b.span.clone(),
                ));
            }
            lists.push(self.lin(bi, depth + 1)?);
            direct_rev.push(bi);
        }
        self.on_stack.remove(&i);

        let mut result = vec![i];
        if !direct_rev.is_empty() {
            lists.push(direct_rev);
            c3_merge(
                lists,
                &mut result,
                &self.contracts[i].name,
                &self.contracts[i].span,
            )?;
        }
        if result.len() > MAX_LINEARIZED {
            return Err(diag(
                codes::FE402_TOO_LARGE_SOL,
                format!("linearized base count exceeds {MAX_LINEARIZED}"),
                self.contracts[i].span.clone(),
            ));
        }
        self.memo.insert(i, result.clone());
        Ok(result)
    }
}

/// The C3 merge: repeatedly take the head of the first list that appears in NO other list's tail,
/// append it to `result`, and remove it from every list — until all lists are empty. If no list's
/// head is a valid candidate, the hierarchy is non-linearizable (contradictory base orderings) →
/// FE471 (solc rejects it identically). Bounded: every step removes one element from finite lists.
fn c3_merge(
    mut lists: Vec<Vec<usize>>,
    result: &mut Vec<usize>,
    name: &str,
    span: &Range<usize>,
) -> Result<(), FrontendDiag> {
    loop {
        lists.retain(|l| !l.is_empty());
        if lists.is_empty() {
            return Ok(());
        }
        let mut head: Option<usize> = None;
        for l in &lists {
            let cand = l[0];
            let in_some_tail = lists.iter().any(|m| m.len() > 1 && m[1..].contains(&cand));
            if !in_some_tail {
                head = Some(cand);
                break;
            }
        }
        let Some(h) = head else {
            return Err(diag(
                codes::FE471_NON_LINEARIZABLE_SOL,
                format!(
                    "non-linearizable inheritance hierarchy for `{name}` (contradictory base order)"
                ),
                span.clone(),
            ));
        };
        result.push(h);
        for l in &mut lists {
            l.retain(|&x| x != h);
        }
    }
}

/// SOL-XFILE PR4/L3: a base constructor is METADATA-ONLY (a droppable no-op) iff every statement is
/// a scalar `Assign` with `op ==` to a field NOT in the merged real state (a dropped string-metadata
/// field like ERC20's `_name`/`_symbol`), from a side-effect-free value (a bare identifier / number /
/// bool), with no base-calls of its own. Dropping it changes no real state and drops no side effect;
/// anything else (a real-field write, arithmetic, a call, an `if`, a nested base-call) → non-metadata,
/// and the caller rejects FE468.
fn is_metadata_only_ctor(ctor: &Constructor, real_state: &HashSet<&str>) -> bool {
    ctor.base_calls.is_empty()
        && ctor.body.iter().all(|s| match s {
            Stmt::Assign {
                target,
                op: AssignOp::Eq,
                value,
                ..
            } => !real_state.contains(target.as_str()) && is_pure_value(value),
            _ => false,
        })
}

/// A value with no side effect and no dependence on runtime state that a dropped assignment could
/// silently discard: a bare identifier (a ctor param), a numeric literal, or a bool literal.
fn is_pure_value(e: &Expr) -> bool {
    matches!(e, Expr::Var(..) | Expr::Num(..) | Expr::Bool(..))
}

/// Per-member merge over the linearization `lin` (most-derived-first). Produces ONE flat concrete
/// `Contract`. Each rule fails closed (EX-2..EX-5):
/// - **functions** — derived-wins by name; a same-name base function with a DIFFERENT signature is
///   an inherited overload SIGIL can't represent → FE420 (never silently drop a function).
/// - **modifiers** — derived-wins by name; the FULL `Modifier{name, body}` from the most-derived
///   definer is carried (EX-3: carrying only the name would leave a stale/empty guard body).
/// - **state** — most-base-first (the storage layout); a same name in two contracts is a SHADOW →
///   FE472 (no merge path can mis-resolve which field a read/write targets).
/// - **structs/enums** — a same type name declared in two contracts is a Solidity declaration
///   conflict → FE473.
/// - **constructor** — SOL-XFILE PR4/L3: the deployed contract's OWN ctor; its base-calls are
///   reduced (an all-literal call to a metadata-only base → dropped; anything else → FE468).
fn merge(contracts: &[Contract], main_idx: usize, lin: &[usize]) -> Result<Contract, FrontendDiag> {
    let main = &contracts[main_idx];

    // SOL-HARDEN C1: reject a same-contract duplicate modifier/function BEFORE the name-keyed
    // derived-wins dedup below silently collapses it (which would mask desugar's FE450 / check's
    // FE420 in ANY ≥2-contract file and compile the function guarded by the FIRST — possibly no-op —
    // body). Runs on `lin` (the only contracts whose members reach the merged output).
    reject_intra_contract_dupes(contracts, lin)?;

    // FUNCTIONS — derived-wins by (name, arity) (lin is most-derived-first); keep-first-seen.
    // SOL-XFILE PR3/OVL: keying by ARITY (not just name) KEEPS a same-name/different-arity overload
    // set (e.g. ERC20's `_approve` 3-arg + 4-arg) — `desugar::disambiguate_overloads` mangles them to
    // unique names later. A same (name, arity) with DIFFERENT parameter types is a same-arity overload
    // that arg-count cannot disambiguate → FE420.
    let mut functions: Vec<Function> = Vec::new();
    let mut fn_sig: HashMap<(String, usize), Vec<String>> = HashMap::new();
    for &i in lin {
        for f in &contracts[i].functions {
            let sig = fn_signature(f);
            let key = (f.name.clone(), f.params.len());
            match fn_sig.get(&key) {
                None => {
                    fn_sig.insert(key, sig);
                    functions.push(f.clone());
                }
                Some(kept) => {
                    if *kept != sig {
                        // Same name AND arity but different parameter types — a same-arity overload.
                        return Err(diag(
                            codes::FE420_BAD_IDENTIFIER_SOL,
                            format!(
                                "overload of `{}` with the same arity but different parameter types cannot be flattened — SIGIL methods don't overload and arg-count cannot disambiguate them",
                                f.name
                            ),
                            f.span.clone(),
                        ));
                    }
                    // Same (name, arity, types) → a faithful override; the derived body (kept) wins.
                }
            }
        }
        if functions.len() > MAX_FUNCTIONS {
            return Err(diag(
                codes::FE402_TOO_LARGE_SOL,
                "too many functions in the merged contract",
                main.span.clone(),
            ));
        }
    }
    // SOL-XFILE PR2/L2: a bodiless (`virtual`, no `{ }`) function that SURVIVED the derived-wins
    // merge means no contract in the linearization implemented it — the flattened concrete is
    // itself abstract and cannot emit a body → FE475 (fail-closed). An overridden bodiless was
    // already dropped above (the bodied derived, seen first, won).
    if let Some(f) = functions.iter().find(|f| f.bodiless) {
        return Err(diag(
            codes::FE475_ABSTRACT_FUNCTION_SOL,
            format!(
                "abstract function `{}` is never implemented in the flattened contract (a `virtual` with no body survives the merge)",
                f.name
            ),
            f.span.clone(),
        ));
    }

    // MODIFIERS — derived-wins by name, carry the full body.
    let mut modifiers: Vec<Modifier> = Vec::new();
    let mut mod_seen: HashSet<String> = HashSet::new();
    for &i in lin {
        for m in &contracts[i].modifiers {
            if mod_seen.insert(m.name.clone()) {
                modifiers.push(m.clone());
            }
        }
    }

    // STRUCTS / ENUMS — a same type name in two contracts is a declaration conflict → FE473.
    let structs = merge_named_types(
        contracts,
        lin,
        |c| &c.structs,
        |s: &Struct| &s.name,
        "struct",
    )?;
    let enums = merge_named_types(contracts, lin, |c| &c.enums, |e: &Enum| &e.name, "enum")?;

    // STATE — most-base-first (storage layout); a shadowed name → FE472.
    let mut state: Vec<StateVar> = Vec::new();
    let mut state_seen: HashMap<String, String> = HashMap::new(); // field → declaring contract
    for &i in lin.iter().rev() {
        for sv in &contracts[i].state {
            if let Some(prev) = state_seen.get(&sv.name) {
                return Err(diag(
                    codes::FE472_STATE_SHADOW_SOL,
                    format!(
                        "state variable `{}` is shadowed (declared in both `{}` and `{}`)",
                        sv.name, prev, contracts[i].name
                    ),
                    sv.span.clone(),
                ));
            }
            state_seen.insert(sv.name.clone(), contracts[i].name.clone());
            state.push(sv.clone());
        }
    }

    // CONSTRUCTOR — SOL-XFILE PR4/L3: the metadata-constructor reduction (fail-closed by default).
    // Step 1: a base (non-main) constructor is DROPPED (not carried) iff it is METADATA-ONLY — its
    // body assigns ONLY dropped string-metadata fields (targets NOT in the merged real state) from
    // side-effect-free values, with no base-calls of its own. This makes OZ's `constructor(string
    // name_, string symbol_) { _name = name_; _symbol = symbol_; }` a no-op (the strings are dropped
    // at parse). A base ctor that writes a REAL state field (or runs any other logic) → FE468.
    let real_state: HashSet<&str> = state_seen.keys().map(|s| s.as_str()).collect();
    for &i in lin {
        if i == main_idx {
            continue;
        }
        if let Some(bc) = &contracts[i].constructor
            && !is_metadata_only_ctor(bc, &real_state)
        {
            return Err(diag(
                codes::FE468_BASE_CONSTRUCTOR_SOL,
                format!(
                    "base contract `{}` declares a constructor that runs real init logic — only a dropped-metadata base constructor (e.g. ERC20's `name`/`symbol`) reduces to a no-op; base-constructor chaining is otherwise unsupported",
                    contracts[i].name
                ),
                bc.span.clone(),
            ));
        }
    }
    // Step 2: the deployed contract's OWN constructor is carried, with its base-calls VALIDATED and
    // cleared. Each `Base(args)` must have all-LITERAL arguments (a literal has no effect and the
    // base ctor it feeds is metadata-only per step 1) and name an actual linearized base; else FE468.
    let mut constructor: Option<Constructor> = main.constructor.clone();
    if let Some(ctor) = &mut constructor {
        let lin_names: HashSet<&str> = lin.iter().map(|&i| contracts[i].name.as_str()).collect();
        for bc in &ctor.base_calls {
            if !bc.all_literal {
                return Err(diag(
                    codes::FE468_BASE_CONSTRUCTOR_SOL,
                    format!(
                        "base-constructor call `{}(…)` has a non-literal argument — only an all-literal call (e.g. `ERC20(\"Name\", \"SYM\")`) reduces to a no-op; passing computed values to a base constructor is unsupported",
                        bc.name
                    ),
                    bc.span.clone(),
                ));
            }
            if !lin_names.contains(bc.name.as_str()) {
                return Err(diag(
                    codes::FE468_BASE_CONSTRUCTOR_SOL,
                    format!(
                        "base-constructor call names `{}`, which is not a base of the deployed contract",
                        bc.name
                    ),
                    bc.span.clone(),
                ));
            }
        }
        ctor.base_calls.clear();
    }

    // POST-ASSERT (EX-3 backstop): every applied modifier name has a surviving decl. A merge that
    // silently dropped a guard fails LOUDLY here, never silently — FE500.
    for f in &functions {
        for applied in &f.modifiers {
            if !modifiers.iter().any(|m| m.name == applied.name) {
                return Err(diag(
                    codes::FE500_INTERNAL_MALFORMED_SOL,
                    format!(
                        "internal: applied modifier `{}` on `{}` has no declaration after merge",
                        applied.name, f.name
                    ),
                    f.span.clone(),
                ));
            }
        }
    }

    Ok(Contract {
        name: main.name.clone(),
        kind: ContractKind::Concrete,
        bases: Vec::new(),
        structs,
        state,
        functions,
        modifiers,
        constructor,
        enums,
        span: main.span.clone(),
    })
}

/// Merge a named-type member list (structs or enums) across the linearization, most-base-first.
/// A type name declared in two contracts is a Solidity declaration conflict → FE473.
fn merge_named_types<T: Clone>(
    contracts: &[Contract],
    lin: &[usize],
    pick: impl Fn(&Contract) -> &Vec<T>,
    name_of: impl Fn(&T) -> &str,
    kind: &str,
) -> Result<Vec<T>, FrontendDiag> {
    let mut out: Vec<T> = Vec::new();
    let mut seen: HashMap<String, String> = HashMap::new(); // type name → declaring contract
    for &i in lin.iter().rev() {
        for t in pick(&contracts[i]) {
            let tn = name_of(t);
            if let Some(prev) = seen.get(tn) {
                return Err(diag(
                    codes::FE473_CONFLICTING_TYPE_SOL,
                    format!(
                        "{kind} `{tn}` is declared in both `{prev}` and `{}` (conflicting declaration)",
                        contracts[i].name
                    ),
                    0..0,
                ));
            }
            seen.insert(tn.to_string(), contracts[i].name.clone());
            out.push(t.clone());
        }
    }
    Ok(out)
}

/// A function's signature = its name plus its parameter types (rendered canonically). Two functions
/// with the same name but different signatures are overloads; with the same signature, an override.
fn fn_signature(f: &Function) -> Vec<String> {
    f.params.iter().map(|p| render_type(&p.ty)).collect()
}

fn render_type(t: &TypeRef) -> String {
    match t {
        // Canonicalize Solidity's type ALIASES so a faithful override (`f(uint)` over `f(uint256)`)
        // compares equal — `uint`≡`uint256`, `int`≡`int256`. Only true synonyms collapse; distinct
        // widths (`uint8` vs `uint256`) stay distinct, so the dangerous inverse (two different types
        // rendering to one string → a silently merged overload) cannot occur.
        TypeRef::Scalar { name, .. } => match name.as_str() {
            "uint" => "uint256".to_string(),
            "int" => "int256".to_string(),
            other => other.to_string(),
        },
        TypeRef::Mapping { key, value, .. } => {
            format!("mapping({}=>{})", render_type(key), render_type(value))
        }
        // SOL-AIRDROP: canonicalize a dynamic array as `<elem>[]` so an array param compares
        // distinct from its scalar element (overload/override signature fidelity).
        TypeRef::Array { elem, .. } => format!("{}[]", render_type(elem)),
    }
}

/// SOL-HARDEN C1 — reject a duplicate modifier or function name declared WITHIN a single contract,
/// before `merge`'s cross-contract dedup keys on name and cannot tell a same-contract duplicate
/// (solc-illegal, ambiguous) from a legal cross-contract override.
///
/// Scope proof (why functions + modifiers are the COMPLETE set): of the six merged declaration kinds,
/// only functions (`merge` FUNCTIONS loop) and modifiers (MODIFIERS loop) dedup keep-first; state
/// (FE472), structs/enums (FE473 via `merge_named_types`) and the constructor (FE463, rejected at
/// parse per contract) each REJECT-on-repeat already, so a same-contract duplicate of those never
/// silently merges. This pass therefore covers exactly the two masked kinds.
///
/// EX-1: each contract is scanned in ISOLATION with a FRESH set, read from its own pristine member
/// list — a base AND a derived both declaring `m` (a legal override) is never flagged; only a
/// within-one-contract duplicate rejects. Codes mirror the downstream gates exactly (FE450 =
/// `inline_modifiers`; FE420 = `check::seen_fns`) so the single-contract fast-path fixtures don't flip.
fn reject_intra_contract_dupes(contracts: &[Contract], lin: &[usize]) -> Result<(), FrontendDiag> {
    for &i in lin {
        let c = &contracts[i];
        let mut seen_mods: HashSet<&str> = HashSet::new();
        for m in &c.modifiers {
            if !seen_mods.insert(m.name.as_str()) {
                return Err(diag(
                    codes::FE450_DUPLICATE_MODIFIER_SOL,
                    format!("duplicate modifier declaration `{}`", m.name),
                    m.span.clone(),
                ));
            }
        }
        // SOL-XFILE PR3/OVL: same-name functions in one contract are Solidity OVERLOADS. Distinct
        // ARITIES are disambiguated later (`desugar::disambiguate_overloads` mangles them by arg
        // count); a same-name SAME-arity pair cannot be told apart by arg count → FE420 (fail-closed).
        let mut seen_fns: HashSet<(&str, usize)> = HashSet::new();
        for f in &c.functions {
            if !seen_fns.insert((f.name.as_str(), f.params.len())) {
                return Err(diag(
                    codes::FE420_BAD_IDENTIFIER_SOL,
                    format!(
                        "duplicate function `{}` (same name AND arity) — Solidity same-arity overloading is unsupported (SIGIL impl methods must be uniquely named)",
                        f.name
                    ),
                    f.span.clone(),
                ));
            }
        }
    }
    Ok(())
}

fn diag(code: &'static str, msg: impl Into<String>, span: Range<usize>) -> FrontendDiag {
    FrontendDiag::new(code, msg, span)
}
