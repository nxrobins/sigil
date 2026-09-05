//! The name-resolution pass: `resolve` maps a parsed `Program` to a
//! `ResolvedProgram` or a `Vec<Diagnostic>` -- assigning `DefId`s,
//! building per-module `UseScope`s, detecting `use`-graph cycles, and
//! running the duplicate-name census over every flat member-name
//! namespace.
//!
//! Invariants owned here:
//! - `DefId`s come from one global source-preorder counter (module, then
//!   its named items): clean programs get an injective, gap-free stream.
//!   The self-hosted resolver is differentially pinned against this file
//!   as the Rust oracle (docs/specs/sh-name-resolution.md;
//!   `crates/sigil-runtime/tests/name_resolution_differential.rs`), so
//!   renumbering here is an output-changing act on that boundary.
//! - The census `match item` in `resolve_module_items` is TOTAL over
//!   `Item` (no `_` arm): a new declaration kind fails to compile until
//!   its member-name namespaces are classified -- the structural end of
//!   the fail-open duplicate-name class. `tests/duplicate_name_census.rs`
//!   pins which namespaces reject and which remain known gaps.
//! - Module-name checks run in a pinned order -- N011 (invalid name)
//!   before N012 (case collision) before N001 (exact duplicate) -- and
//!   the sh-name-resolution differential covers that precedence.
//!
//! Failure discipline: fail-closed -- ANY diagnostic yields `Err`; no
//! partial `ResolvedProgram` escapes. Codes emitted here: N001-N007,
//! N009, N011-N017. The N007 "did you mean" hint attaches a
//! machine-applicable edit only at Levenshtein distance <= 1 (E3;
//! `tests/suggested_edits_p001_n007.rs`).

use std::collections::{HashMap, HashSet};

use crate::{
    ast::{ActorDef, Item, Module, Param, Program, RecordDef},
    diagnostics::{Diagnostic, SuggestedEdit, codes},
    span::Span,
    trace,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedProgram {
    pub ast: Program,
    pub modules: Vec<ResolvedModule>,
}

/// Per-module mapping from a `use`-imported alias to the fully-qualified
/// module name it resolves to.
///
/// `use sigil::fs;` produces an entry `("fs" → "fs")` (the leaf segment is
/// the alias; the path's module name is `fs`). For `use sigil::fs;` the
/// alias is "fs" and the target module is also "fs". (For v1, `use` paths
/// are always shaped `<crate>::<module>` — see `parse_use`. Function-level
/// imports `use sigil::fs::{read, write};` are deferred to v2.)
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct UseScope {
    pub aliases: HashMap<String, String>,
}

impl UseScope {
    pub fn lookup(&self, alias: &str) -> Option<&str> {
        self.aliases.get(alias).map(String::as_str)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedModule {
    pub def_id: DefId,
    pub name: String,
    pub span: Span,
    pub items: Vec<ResolvedItem>,
    /// `use`-imported aliases for this module, validated against the
    /// program's module set during `resolve()`.
    pub use_scope: UseScope,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedItem {
    pub def_id: DefId,
    pub name: String,
    pub kind: ResolvedItemKind,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResolvedItemKind {
    Const,
    Function,
    Actor,
    CapabilityType,
    Record,
    Enum,
    Impl,
}

/// Per Phase 5a-1.5 / I25. Module names must be lowercase alphanumeric +
/// underscores, starting with letter or underscore. Mirrors most language
/// conventions and avoids platform-dependent case-sensitivity ambiguity.
pub(crate) fn is_valid_module_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_lowercase() || first == '_') {
        return false;
    }
    chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
}

pub fn resolve(program: &Program) -> Result<ResolvedProgram, Vec<Diagnostic>> {
    let mut diagnostics = Vec::new();
    let mut seen_modules = HashMap::<String, Span>::new();
    // For N012 (case-collision): track lowercase-name → original-name + span.
    let mut seen_lowercase = HashMap::<String, (String, Span)>::new();
    let mut next_def_id = 0u32;
    let mut modules = Vec::new();

    // First pass: collect all module names so `use` resolution can validate
    // that imported modules actually exist.
    let module_names: HashSet<String> = program.modules.iter().map(|m| m.name.clone()).collect();

    for module in &program.modules {
        // N011: well-formed module name.
        if !is_valid_module_name(&module.name) {
            diagnostics.push(Diagnostic::error(
                codes::N011,
                format!(
                    "module name `{}` is invalid; must match `^[a-z_][a-z0-9_]*$`",
                    module.name
                ),
                Some(module.span),
            ));
            continue;
        }

        // N012: case-collision check (e.g. `fs` and `Fs`). Done before the
        // exact-name N001 check so case-only-different reports as N012, not
        // N001.
        let lower = module.name.to_ascii_lowercase();
        if let Some((other_name, other_span)) = seen_lowercase.get(&lower)
            && other_name != &module.name
        {
            diagnostics.push(Diagnostic::error(
                codes::N012,
                format!(
                    "module names `{}` and `{}` differ only in case; rename one",
                    other_name, module.name
                ),
                Some(other_span.join(module.span)),
            ));
            continue;
        }
        seen_lowercase.insert(lower, (module.name.clone(), module.span));

        if let Some(previous) = seen_modules.insert(module.name.clone(), module.span) {
            diagnostics.push(Diagnostic::error(
                codes::N001,
                format!("duplicate module `{}`", module.name),
                Some(previous.join(module.span)),
            ));
            continue;
        }

        let module_def_id = DefId(next_def_id);
        next_def_id += 1;

        let (items, item_diagnostics, next_id) = resolve_module_items(module, next_def_id);
        next_def_id = next_id;
        diagnostics.extend(item_diagnostics);

        let (use_scope, scope_diagnostics) = build_use_scope(module, &module_names);
        diagnostics.extend(scope_diagnostics);

        modules.push(ResolvedModule {
            def_id: module_def_id,
            name: module.name.clone(),
            span: module.span,
            items,
            use_scope,
        });
    }

    // Second pass: cycle detection on the use-induced dependency graph.
    diagnostics.extend(detect_use_cycles(&modules));

    if diagnostics.is_empty() {
        Ok(ResolvedProgram {
            ast: program.clone(),
            modules,
        })
    } else {
        Err(diagnostics)
    }
}

/// Iterative Levenshtein distance with one row of memo. O(m·n) time, O(min(m,n)) space.
/// Used to suggest "did you mean" alternatives in N007.
fn levenshtein(a: &str, b: &str) -> usize {
    if a.is_empty() {
        return b.chars().count();
    }
    if b.is_empty() {
        return a.chars().count();
    }
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b_chars.len()).collect();
    let mut curr: Vec<usize> = vec![0; b_chars.len() + 1];
    for (i, ca) in a_chars.iter().enumerate() {
        curr[0] = i + 1;
        for (j, cb) in b_chars.iter().enumerate() {
            let cost = if ca == cb { 0 } else { 1 };
            curr[j + 1] = (curr[j] + 1).min(prev[j + 1] + 1).min(prev[j] + cost);
        }
        std::mem::swap(&mut prev, &mut curr);
    }
    prev[b_chars.len()]
}

/// Format the "did you mean" suffix for an N007 hint: top up to 5 candidates
/// from `module_names` ordered by Levenshtein distance to `target`.
/// Returns an empty string if the program has no modules at all.
fn suggest_modules(target: &str, module_names: &HashSet<String>) -> String {
    if module_names.is_empty() {
        return String::new();
    }
    let mut ranked: Vec<(usize, &String)> = module_names
        .iter()
        .map(|name| (levenshtein(target, name), name))
        .collect();
    ranked.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(b.1)));
    let suggestions: Vec<&str> = ranked
        .iter()
        .take(5)
        .map(|(_, name)| name.as_str())
        .collect();
    format!(" available: [{}]", suggestions.join(", "))
}

/// The single nearest module to `target` IF within Levenshtein distance 1
/// (a near-certain typo). This is the high-confidence bar for a *machine-
/// applicable edit* — strictly tighter than `suggest_modules`'s hint list, so a
/// genuinely-missing module (distance ≥ 2) gets no rename suggestion (E3).
fn closest_module(target: &str, module_names: &HashSet<String>) -> Option<String> {
    module_names
        .iter()
        .map(|name| (levenshtein(target, name), name))
        .filter(|(d, _)| *d <= 1)
        .min_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(b.1)))
        .map(|(_, name)| name.clone())
}

/// Build the UseScope for a single module. Validates each `use sigil::M;`
/// path against the set of modules in the compilation unit; emits N007 for
/// unresolved paths.
///
/// Path shape accepted in v1: `<crate>::<module>` (two segments). The crate
/// segment is `sigil` (the stdlib root) but we accept any crate name as a
/// pass-through since we don't yet have multi-crate compilation. Single-segment
/// `use M;` is also accepted as a self-reference.
fn build_use_scope(module: &Module, module_names: &HashSet<String>) -> (UseScope, Vec<Diagnostic>) {
    let mut diagnostics = Vec::new();
    let mut scope = UseScope::default();

    for item in &module.items {
        let Item::UseDecl(decl) = item else { continue };

        // Resolve the path. Last segment is the module name being imported;
        // it doubles as the alias (no `as` syntax in v1).
        let segments = &decl.path.segments;
        let target_module = match segments.as_slice() {
            [name] => name.clone(),
            [_crate, name] => name.clone(),
            // v2: function-level imports `use sigil::fs::{read, write};`
            // and renaming `use sigil::fs as filesystem;` are not supported.
            _ => {
                diagnostics.push(Diagnostic::error(
                    codes::N007,
                    format!(
                        "unsupported `use` path shape `{}`: only `use <crate>::<module>;` is supported in v1",
                        decl.path.display_name()
                    ),
                    Some(decl.span),
                ));
                continue;
            }
        };

        if !module_names.contains(&target_module) {
            let mut diag = Diagnostic::error(
                codes::N007,
                format!(
                    "`use {}` does not resolve to any module in this compilation unit;{}",
                    decl.path.display_name(),
                    suggest_modules(&target_module, module_names)
                ),
                Some(decl.span),
            );
            // High-confidence typo (distance <= 1) → machine-applicable replace
            // edit over the path, with the last segment corrected so it is both
            // apply-correct and renders as the fixed path. Genuinely-missing
            // modules (distance >= 2) get no edit (E3).
            if let Some(closest) = closest_module(&target_module, module_names) {
                let mut fixed = segments.clone();
                if let Some(last) = fixed.last_mut() {
                    *last = closest;
                }
                diag = diag.with_suggested_edits(vec![SuggestedEdit {
                    start: decl.path.span.start,
                    end: decl.path.span.end,
                    replacement: fixed.join("::"),
                }]);
            }
            diagnostics.push(diag);
            continue;
        }

        // Tools cannot `use` themselves.
        if target_module == module.name {
            diagnostics.push(Diagnostic::error(
                codes::N007,
                format!("module `{}` cannot `use` itself", module.name),
                Some(decl.span),
            ));
            continue;
        }

        // Duplicate `use` for the same module-as-alias collapses silently —
        // no diagnostic, just one entry. (Use of *different* aliases for the
        // same module is also fine; only ambiguous symbol lookup is an
        // error, surfaced as N008 at the call site.)
        scope.aliases.insert(target_module.clone(), target_module);
    }

    trace::use_scope_built(&trace::UseScopeBuilt {
        module: &module.name,
        alias_count: scope.aliases.len(),
    });

    (scope, diagnostics)
}

/// Format a cycle path with summarization per Phase 5a-1.5 / Op B.
/// Path of length ≤ 7 displays inline. Longer cycles render as
/// `[A → B → C → D → E → ... → Y → Z]` (first 5 + last 2 with ellipsis).
fn format_cycle_path(path: &[String]) -> String {
    if path.len() <= 7 {
        return format!("[{}]", path.join(" → "));
    }
    let head: Vec<&str> = path.iter().take(5).map(String::as_str).collect();
    let tail: Vec<&str> = path[path.len() - 2..].iter().map(String::as_str).collect();
    format!(
        "[{} → ... ({} more) → {}]",
        head.join(" → "),
        path.len() - 7,
        tail.join(" → ")
    )
}

/// Walk the use-edge graph (module A `use`s module B) and emit N009 if a
/// cycle is found. Uses iterative DFS with three-color coloring (white /
/// gray / black) to detect back-edges. The full DFS path stack is
/// recorded so the diagnostic can render the cycle (with summarization
/// for long cycles).
fn detect_use_cycles(modules: &[ResolvedModule]) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let by_name: HashMap<&str, &ResolvedModule> =
        modules.iter().map(|m| (m.name.as_str(), m)).collect();

    #[derive(Clone, Copy, PartialEq, Eq)]
    enum Color {
        White,
        Gray,
        Black,
    }

    let mut color: HashMap<&str, Color> = modules
        .iter()
        .map(|m| (m.name.as_str(), Color::White))
        .collect();
    let mut reported: HashSet<String> = HashSet::new();

    for start in modules {
        if color[start.name.as_str()] != Color::White {
            continue;
        }
        // Iterative DFS. Each stack frame is (node, child_iterator).
        // The path-so-far is reconstructed from the stack's nodes.
        let mut stack: Vec<(&str, std::collections::hash_map::Iter<'_, String, String>)> =
            Vec::new();
        color.insert(start.name.as_str(), Color::Gray);
        stack.push((start.name.as_str(), start.use_scope.aliases.iter()));

        while let Some((node, mut iter)) = stack.pop() {
            if let Some((_, target)) = iter.next() {
                // Push the parent back with the advanced iterator.
                stack.push((node, iter));
                let target_str = target.as_str();
                match color.get(target_str).copied() {
                    Some(Color::White) => {
                        if let Some(target_mod) = by_name.get(target_str) {
                            color.insert(target_mod.name.as_str(), Color::Gray);
                            stack.push((
                                target_mod.name.as_str(),
                                target_mod.use_scope.aliases.iter(),
                            ));
                        }
                    }
                    Some(Color::Gray) => {
                        // Back-edge → cycle. Reconstruct the cycle from
                        // the stack: find target_str in the stack's nodes
                        // and slice from there.
                        let cycle_start = stack.iter().position(|(n, _)| *n == target_str);
                        if let Some(idx) = cycle_start {
                            let mut path: Vec<String> =
                                stack[idx..].iter().map(|(n, _)| (*n).to_owned()).collect();
                            path.push(target_str.to_owned()); // close the loop
                            // Dedup-key: the canonical cycle (rotated to
                            // start at lex-smallest node) prevents
                            // double-reporting from different DFS roots.
                            let canonical_key = canonical_cycle_key(&path);
                            if reported.insert(canonical_key) {
                                let span =
                                    by_name.get(target_str).map(|m| m.span).unwrap_or_default();
                                trace::cycle(&trace::CycleDetected {
                                    path_len: path.len(),
                                    head: path.first().map(String::as_str).unwrap_or(""),
                                    tail: path.last().map(String::as_str).unwrap_or(""),
                                });
                                diagnostics.push(Diagnostic::error(
                                    codes::N009,
                                    format!(
                                        "cyclic module dependency: {}",
                                        format_cycle_path(&path)
                                    ),
                                    Some(span),
                                ));
                            }
                        }
                    }
                    _ => {}
                }
            } else {
                // Done with this node; mark black.
                color.insert(node, Color::Black);
            }
        }
    }

    diagnostics
}

/// Cycle dedup key: the lex-smallest rotation of the cycle (excluding the
/// closing duplicate node). Different DFS entry points hitting the same
/// cycle should produce identical keys.
fn canonical_cycle_key(path: &[String]) -> String {
    if path.is_empty() {
        return String::new();
    }
    // Drop the closing duplicate (path[0] == path[last]).
    let core: &[String] = if path.len() >= 2 && path[0] == path[path.len() - 1] {
        &path[..path.len() - 1]
    } else {
        path
    };
    if core.is_empty() {
        return String::new();
    }
    let min_idx = core
        .iter()
        .enumerate()
        .min_by(|a, b| a.1.cmp(b.1))
        .map(|(i, _)| i)
        .unwrap_or(0);
    let mut rotated: Vec<&str> = core[min_idx..].iter().map(String::as_str).collect();
    rotated.extend(core[..min_idx].iter().map(String::as_str));
    rotated.join("→")
}

fn resolve_module_items(
    module: &Module,
    mut next_def_id: u32,
) -> (Vec<ResolvedItem>, Vec<Diagnostic>, u32) {
    let mut diagnostics = Vec::new();
    let mut seen = HashMap::<String, Span>::new();
    let mut items = Vec::new();

    for item in &module.items {
        if let Some(name) = item.name() {
            if let Some(previous) = seen.insert(name.to_owned(), item.span()) {
                diagnostics.push(Diagnostic::error(
                    codes::N002,
                    format!("duplicate definition `{name}` in module `{}`", module.name),
                    Some(previous.join(item.span())),
                ));
                continue;
            }

            items.push(ResolvedItem {
                def_id: DefId(next_def_id),
                name: name.to_owned(),
                kind: resolve_item_kind(item),
                span: item.span(),
            });
            next_def_id += 1;

            if let Item::ActorDef(actor) = item {
                let actor_diagnostics = check_duplicate_handlers(module, actor);
                diagnostics.extend(actor_diagnostics);
                diagnostics.extend(check_actor_scope_conflicts(module, actor));
            }

            if let Item::FnDef(function) = item {
                diagnostics.extend(check_duplicate_params(
                    module,
                    "function",
                    &function.name,
                    &function.params,
                ));
            }

            if let Item::RecordDef(record) = item {
                diagnostics.extend(check_duplicate_record_fields(module, record));
            }
        }

        // Duplicate-name census (N013–N017). Every declarable namespace that
        // carries a flat list of member identifiers must reject duplicates —
        // historically each was checked (or NOT) by its own bespoke pass, so
        // the ones nobody wrote a pass for compiled fail-open (a duplicate
        // silently shadowed or collided). This TOTAL match over `Item` is the
        // structural fence: a NEW declaration kind fails to compile here until
        // its member-name namespaces are classified — you cannot add an
        // `Item` variant and silently skip its duplicate-name checking.
        //
        // OUTSIDE the `if let Some(name)` guard on purpose: `state`/`impl` are
        // NAMELESS (`Item::name()` is `None`), so gating on a top-level name
        // would silently skip them — the exact fail-open this census ends.
        //
        // KNOWN GAPS (still fail-open; each needs dispatch/coherence-aware
        // handling, tracked in tests/duplicate_name_census.rs): effect-op
        // names, trait-method names, cross-impl-block method names, extern-fn
        // params, and in-pattern binders (`let (a, a)`, `match V(x, x)`).
        match item {
            Item::EnumDef(e) => {
                let mname = module.name.clone();
                let ename = e.name.clone();
                diagnostics.extend(check_duplicate_member_names(
                    e.variants.iter().map(|v| (v.name.as_str(), v.span)),
                    codes::N014,
                    |n| format!("duplicate variant `{n}` in enum `{ename}` of module `{mname}`"),
                ));
                diagnostics.extend(check_duplicate_type_params(
                    module,
                    "enum",
                    &e.name,
                    &e.type_params,
                ));
            }
            Item::CapTypeDef(c) => {
                let mname = module.name.clone();
                let cname = c.name.clone();
                diagnostics.extend(check_duplicate_member_names(
                    c.authorities.iter().map(|a| (a.as_str(), c.span)),
                    codes::N015,
                    |n| {
                        format!(
                            "duplicate authority `{n}` in cap type `{cname}` of module `{mname}`"
                        )
                    },
                ));
            }
            Item::StateDef(s) => {
                let mname = module.name.clone();
                let sname = s.name.clone();
                diagnostics.extend(check_duplicate_member_names(
                    s.states.iter().map(|st| (st.as_str(), s.span)),
                    codes::N016,
                    |n| format!("duplicate state `{n}` in `state {sname}` of module `{mname}`"),
                ));
            }
            Item::FnDef(f) => {
                // Params → N005 (via the `if let Item::FnDef` block above);
                // type params → N017 here.
                diagnostics.extend(check_duplicate_type_params(
                    module,
                    "function",
                    &f.name,
                    &f.type_params,
                ));
            }
            Item::RecordDef(r) => {
                // Fields → N013 (above); type params → N017 here.
                diagnostics.extend(check_duplicate_type_params(
                    module,
                    "record",
                    &r.name,
                    &r.type_params,
                ));
            }
            // N005 (duplicate parameter) rode ONLY the free-fn and actor
            // init/handler paths; every other param-bearing decl was
            // fail-open — a duplicate silently bound one of the two, and for
            // an impl method that is live, running code. Same code, same
            // helper, the sites that were never wired.
            Item::ImplDef(i) => {
                for method in &i.methods {
                    diagnostics.extend(check_duplicate_params(
                        module,
                        "impl method",
                        &format!("{}::{}", i.type_name, method.name),
                        &method.params,
                    ));
                }
            }
            Item::EffectDecl(e) => {
                for op in &e.ops {
                    diagnostics.extend(check_duplicate_params(
                        module,
                        "effect operation",
                        &format!("{}::{}", e.name, op.name),
                        &op.params,
                    ));
                }
            }
            Item::TraitDef(t) => {
                for method in &t.methods {
                    diagnostics.extend(check_duplicate_params(
                        module,
                        "trait method",
                        &format!("{}::{}", t.name, method.name),
                        &method.params,
                    ));
                }
            }
            // Handled by dedicated passes / other pipeline stages:
            //   ActorDef  → N003 handlers / N004 state fields / N005 params
            //   ImplDef   → T229 impl type params (parser); METHOD-name dedup
            //               across impl blocks is a KNOWN GAP (needs
            //               coherence-aware handling).
            //   EffectDecl / TraitDef → op-/method-NAME dedup is a KNOWN GAP
            //               (needs dispatch-aware handling).
            //   ExternFnDecl → params are unreachable here: the grammar
            //               rejects a duplicate before name-resolution (P002).
            // No member-name list (nothing to dedup):
            //   UseDecl / ConstDef / TypeAlias
            Item::ActorDef(_)
            | Item::ExternFnDecl(_)
            | Item::UseDecl(_)
            | Item::ConstDef(_)
            | Item::TypeAlias(_) => {}
        }
    }

    (items, diagnostics, next_def_id)
}

/// N017: a `fn`/`record`/`enum` type-parameter list `<T, U, ...>` must have
/// unique names. `impl Foo<T, T>` is already caught in the parser (T229);
/// the other three generic-bearing decls were fail-open — a duplicate
/// `<T, T>` collapses to one binding under positional substitution. Closes
/// that per-case asymmetry through the shared census engine.
fn check_duplicate_type_params(
    module: &Module,
    owner_kind: &str,
    owner_name: &str,
    type_params: &[crate::ast::TypeParam],
) -> Vec<Diagnostic> {
    let mname = module.name.clone();
    let oname = owner_name.to_owned();
    let kind = owner_kind.to_owned();
    check_duplicate_member_names(
        type_params.iter().map(|p| (p.name.as_str(), p.span)),
        codes::N017,
        |n| format!("duplicate type parameter `{n}` in {kind} `{oname}` of module `{mname}`"),
    )
}

fn resolve_item_kind(item: &Item) -> ResolvedItemKind {
    match item {
        Item::ConstDef(_) => ResolvedItemKind::Const,
        Item::FnDef(_) => ResolvedItemKind::Function,
        Item::ActorDef(_) => ResolvedItemKind::Actor,
        Item::CapTypeDef(_) => ResolvedItemKind::CapabilityType,
        Item::RecordDef(_) => ResolvedItemKind::Record,
        Item::EnumDef(_) => ResolvedItemKind::Enum,
        Item::ImplDef(_) => ResolvedItemKind::Impl,
        Item::EffectDecl(_) => ResolvedItemKind::Const, // effects are declarations, not items
        Item::ExternFnDecl(_) => ResolvedItemKind::Function,
        // A trait introduces a top-level name (caught for duplicates / coherence)
        // but is not a value type; treat it as a declaration like effects.
        Item::TraitDef(_) => ResolvedItemKind::Const,
        Item::UseDecl(_) => ResolvedItemKind::Const,
        // PR-E4: a type alias introduces a top-level type NAME (caught for duplicate
        // names via Item::name) but is substitutive — resolved in the type universe,
        // not a distinct resolved-item category; treat as a declaration like traits.
        Item::TypeAlias(_) => ResolvedItemKind::Const,
        // Typestate (Epic 1): a `state Name {…}` decl is type-level metadata (its
        // `name()` is None, so it never registers a top-level name); treat it as a
        // declaration like effects/traits.
        Item::StateDef(_) => ResolvedItemKind::Const,
    }
}

fn check_duplicate_handlers(module: &Module, actor: &ActorDef) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut seen = HashMap::<String, Span>::new();

    for handler in &actor.handlers {
        if let Some(previous) = seen.insert(handler.message_name.clone(), handler.span) {
            diagnostics.push(Diagnostic::error(
                codes::N003,
                format!(
                    "duplicate handler `{}` in actor `{}` of module `{}`",
                    handler.message_name, actor.name, module.name
                ),
                Some(previous.join(handler.span)),
            ));
        }
    }

    diagnostics
}

fn check_actor_scope_conflicts(module: &Module, actor: &ActorDef) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut state_fields = HashMap::<String, Span>::new();

    for field in &actor.state_fields {
        if let Some(previous) = state_fields.insert(field.name.clone(), field.span) {
            diagnostics.push(Diagnostic::error(
                codes::N004,
                format!(
                    "duplicate state field `{}` in actor `{}` of module `{}`",
                    field.name, actor.name, module.name
                ),
                Some(previous.join(field.span)),
            ));
        }
    }

    let state_names = state_fields.keys().cloned().collect::<HashSet<_>>();

    if let Some(init) = &actor.init {
        diagnostics.extend(check_duplicate_params(
            module,
            "actor init",
            &actor.name,
            &init.params,
        ));
        diagnostics.extend(check_actor_param_shadowing(
            module,
            actor,
            "init parameter",
            &actor.name,
            &init.params,
            &state_names,
        ));
    }

    for handler in &actor.handlers {
        let handler_name = format!("{}::{}", actor.name, handler.message_name);
        diagnostics.extend(check_duplicate_params(
            module,
            "handler",
            &handler_name,
            &handler.params,
        ));
        diagnostics.extend(check_actor_param_shadowing(
            module,
            actor,
            "handler parameter",
            &handler_name,
            &handler.params,
            &state_names,
        ));
    }

    diagnostics
}

/// N004 analog for records (N013): reject a `record` whose field list declares
/// two fields with the same name. The parser admits the duplicate
/// (`parse_fields_until_rbrace` does no dedup), so without this check a
/// duplicate-field record compiles fail-open — a later field read silently
/// resolves to one of the same-named fields while the other is dead (silent
/// mis-initialization). Untrusted frontends (e.g. Solidity → SIGIL) emit
/// `record`s for their data types, so the trusted compiler is the last line of
/// defense; mirrors the actor-state-field (N004) and enum-payload (T223) checks.
fn check_duplicate_record_fields(module: &Module, record: &RecordDef) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut seen = HashMap::<String, Span>::new();

    for field in &record.fields {
        if let Some(previous) = seen.insert(field.name.clone(), field.span) {
            diagnostics.push(Diagnostic::error(
                codes::N013,
                format!(
                    "duplicate field `{}` in record `{}` of module `{}`",
                    field.name, record.name, module.name
                ),
                Some(previous.join(field.span)),
            ));
        }
    }

    diagnostics
}

/// The generic "a declaration's member-name list must be unique" check —
/// the shared engine behind N013 (record fields), N014 (enum variants),
/// N015 (cap authorities), N016 (protocol states), and N017 (type params).
///
/// Every declarable member-name namespace was historically checked (or NOT)
/// by its own bespoke pass, so the ones nobody wrote a pass for compiled
/// fail-open — a duplicate silently shadowed or collided (the same
/// "a per-case pass forgot a case" family as the Type-walker Fn/Tuple-arm
/// bugs). This routes every flat-identifier-list namespace through ONE
/// engine so the coverage is a census, not scattered luck. `tests/
/// duplicate_name_census.rs` pins which namespaces flow through here.
///
/// `members` is (name, span) in DECLARATION order; the diagnostic anchors
/// the FIRST..=duplicate span (matching N005/N013). When a namespace has no
/// per-member span (authorities/states are bare `Vec<String>`), the caller
/// passes the declaration's own span for every member.
fn check_duplicate_member_names<'a>(
    members: impl IntoIterator<Item = (&'a str, Span)>,
    code: crate::diagnostics::DiagnosticCode,
    message: impl Fn(&str) -> String,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut seen = HashMap::<&str, Span>::new();
    for (name, span) in members {
        if let Some(previous) = seen.insert(name, span) {
            diagnostics.push(Diagnostic::error(
                code,
                message(name),
                Some(previous.join(span)),
            ));
        }
    }
    diagnostics
}

fn check_duplicate_params(
    module: &Module,
    owner_kind: &str,
    owner_name: &str,
    params: &[Param],
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();
    let mut seen = HashMap::<String, Span>::new();

    for param in params {
        if let Some(previous) = seen.insert(param.name.clone(), param.span) {
            diagnostics.push(Diagnostic::error(
                codes::N005,
                format!(
                    "duplicate parameter `{}` in {} `{}` of module `{}`",
                    param.name, owner_kind, owner_name, module.name
                ),
                Some(previous.join(param.span)),
            ));
        }
    }

    diagnostics
}

fn check_actor_param_shadowing(
    module: &Module,
    actor: &ActorDef,
    param_kind: &str,
    owner_name: &str,
    params: &[Param],
    state_names: &HashSet<String>,
) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for param in params {
        if state_names.contains(&param.name) {
            diagnostics.push(Diagnostic::error(
                codes::N006,
                format!(
                    "{} `{}` in `{}` of actor `{}` shadows a state field in module `{}`",
                    param_kind, param.name, owner_name, actor.name, module.name
                ),
                Some(param.span),
            ));
        }
    }

    diagnostics
}
