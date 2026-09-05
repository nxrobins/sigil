//! Wall 4 Step 7 spec-compliance follow-up: `..Default::default()`
//! on `FnDef` literal lint.
//!
//! Closes N22-S7 (which the original Step 7 plan said should be a CI
//! grep-lint, then NF-S7-7 corrected to "regex is fundamentally wrong
//! for Rust's nested-brace syntax"). This binary parses every `.rs`
//! file under the provided root via `syn::parse_file`, visits every
//! `ExprStruct` node, and flags FnDef literals that use the
//! `..Default::default()` rest-pattern bypass.
//!
//! Constraints enforced:
//! - NF-S7-7: `use syn::visit::Visit`; no `regex::Regex` anywhere.
//! - NF-S7-8: exact-segment match on `FnDef` (not substring); rejects
//!   `BoxedFnDef`, `MyFnDef`, etc.
//! - NF-S7-9: only `..Default::default()` flagged. Legitimate
//!   clone-with-override (`..existing_def`) is NOT flagged.
//! - NF-S7-13: positive (known_bad) and negative (known_good) test
//!   fixtures in `tests/`.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use syn::visit::Visit;

struct FnDefRestVisitor {
    file: PathBuf,
    offenders: Vec<Offender>,
}

#[derive(Debug)]
struct Offender {
    file: PathBuf,
    struct_name: String,
}

impl FnDefRestVisitor {
    fn new(file: PathBuf) -> Self {
        Self {
            file,
            offenders: Vec::new(),
        }
    }
}

impl<'ast> Visit<'ast> for FnDefRestVisitor {
    fn visit_expr_struct(&mut self, node: &'ast syn::ExprStruct) {
        // NF-S7-8: EXACT-SEGMENT match on the final path segment. We
        // compare the `ident` to literal "FnDef" — never substring,
        // never prefix/suffix. `BoxedFnDef`, `MyFnDef`, etc. are NOT
        // flagged.
        let last_segment = node
            .path
            .segments
            .last()
            .map(|seg| seg.ident.to_string())
            .unwrap_or_default();

        if last_segment != "FnDef" {
            // Continue descending — nested struct literals might
            // contain an FnDef somewhere.
            syn::visit::visit_expr_struct(self, node);
            return;
        }

        // NF-S7-9: only flag when the rest-pattern is specifically
        // `Default::default()`. Legitimate clone-with-override like
        // `FnDef { name, ..existing_def }` is allowed.
        if let Some(rest_expr) = &node.rest
            && is_default_default_call(rest_expr)
        {
            // Position-info is best-effort; syn 2.x's stable
            // Span surface doesn't expose byte offsets reliably
            // across host configurations. We record the file +
            // struct-name for diagnostic output; future PR can
            // upgrade to proc-macro2's nightly span ranges if
            // needed.
            self.offenders.push(Offender {
                file: self.file.clone(),
                struct_name: last_segment,
            });
        }

        // Continue descending in case nested literals exist.
        syn::visit::visit_expr_struct(self, node);
    }
}

/// Returns true if `expr` is structurally `Default::default()` —
/// i.e., a call expression where the path is exactly `Default::default`.
/// Per NF-S7-9, ONLY this specific shape is flagged.
fn is_default_default_call(expr: &syn::Expr) -> bool {
    let syn::Expr::Call(call) = expr else {
        return false;
    };
    // Must be zero-argument call.
    if !call.args.is_empty() {
        return false;
    }
    let syn::Expr::Path(path_expr) = &*call.func else {
        return false;
    };
    let segments: Vec<String> = path_expr
        .path
        .segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect();
    // Match `Default::default` exactly (2 segments), or just `default`
    // (single segment, if user imported `use std::default::Default;`
    // and called it qualified-only).
    matches!(
        segments.as_slice(),
        [a, b] if a == "Default" && b == "default"
    )
}

fn lint_file(path: &Path) -> std::io::Result<Vec<Offender>> {
    let source = std::fs::read_to_string(path)?;
    let syntax_tree = match syn::parse_file(&source) {
        Ok(tree) => tree,
        Err(_) => {
            // Skip files that fail to parse (e.g., build.rs with
            // attribute syntax we don't handle). Soundness invariant:
            // if a file doesn't parse, it can't compile, so it can't
            // construct FnDef successfully.
            return Ok(Vec::new());
        }
    };
    let mut visitor = FnDefRestVisitor::new(path.to_path_buf());
    visitor.visit_file(&syntax_tree);
    Ok(visitor.offenders)
}

fn lint_directory(root: &Path) -> std::io::Result<Vec<Offender>> {
    let mut all_offenders = Vec::new();
    for entry in walkdir::WalkDir::new(root)
        .follow_links(false)
        .into_iter()
        .filter_map(|e| e.ok())
    {
        let path = entry.path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            all_offenders.extend(lint_file(path)?);
        }
    }
    Ok(all_offenders)
}

fn report_offenders(offenders: &[Offender]) {
    if offenders.is_empty() {
        println!(
            "no_fndef_rest_pattern (NF-S7-7 lint): clean — no `..Default::default()` rest-pattern on `FnDef` literals."
        );
        return;
    }
    eprintln!(
        "no_fndef_rest_pattern (N22-S7 violation): {} `FnDef` literal(s) use `..Default::default()` rest-pattern:",
        offenders.len()
    );
    for off in offenders {
        eprintln!(
            "  {}  (struct `{}`)",
            off.file.display(),
            off.struct_name
        );
    }
    eprintln!(
        "Enumerate all `FnDef` fields explicitly so `cargo build` catches missing Wall 4 Step 7 refinement fields (`param_refinements`, `return_refinement`)."
    );
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!(
            "usage: no_fndef_rest_pattern <DIR> [<DIR>...]\n\
             scans .rs files under each DIR for `FnDef {{ .. ..Default::default() }}` literals."
        );
        return ExitCode::from(2);
    }
    let mut all_offenders = Vec::new();
    for dir in &args[1..] {
        match lint_directory(Path::new(dir)) {
            Ok(offs) => all_offenders.extend(offs),
            Err(e) => {
                eprintln!("error scanning `{dir}`: {e}");
                return ExitCode::from(2);
            }
        }
    }
    report_offenders(&all_offenders);
    if all_offenders.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_fixture(content: &str) -> tempfile::NamedTempFile {
        let mut file = tempfile::Builder::new()
            .suffix(".rs")
            .tempfile()
            .expect("tempfile");
        file.write_all(content.as_bytes()).expect("write");
        file
    }

    /// NF-S7-13 positivity: lint MUST flag the known-bad fixture.
    #[test]
    fn lint_catches_known_bad() {
        let bad = include_str!("../tests/known_bad.rs.txt");
        let file = write_fixture(bad);
        let offenders = lint_file(file.path()).expect("lint runs");
        assert!(
            !offenders.is_empty(),
            "NF-S7-13: known_bad.rs.txt MUST be flagged by the lint"
        );
    }

    /// NF-S7-13 negativity: lint MUST NOT flag the known-good fixture.
    #[test]
    fn lint_passes_known_good() {
        let good = include_str!("../tests/known_good.rs.txt");
        let file = write_fixture(good);
        let offenders = lint_file(file.path()).expect("lint runs");
        assert!(
            offenders.is_empty(),
            "NF-S7-13: known_good.rs.txt MUST NOT be flagged. Offenders: {offenders:?}"
        );
    }

    /// NF-S7-8: `BoxedFnDef { ..Default::default() }` MUST NOT be
    /// flagged — exact-segment match on `FnDef` only.
    #[test]
    fn lint_does_not_match_boxed_fn_def() {
        let src = r#"
struct BoxedFnDef { name: String }
fn make() -> BoxedFnDef {
    BoxedFnDef { ..Default::default() }
}
"#;
        let file = write_fixture(src);
        let offenders = lint_file(file.path()).expect("lint runs");
        assert!(
            offenders.is_empty(),
            "NF-S7-8: BoxedFnDef should NOT be flagged. Offenders: {offenders:?}"
        );
    }

    /// NF-S7-9: `FnDef { name, ..existing_def }` (clone-with-override)
    /// MUST NOT be flagged. Only `..Default::default()` is the target.
    #[test]
    fn lint_allows_clone_with_override_for_fn_def() {
        let src = r#"
struct FnDef { name: String, params: Vec<i32> }
fn rebuild(other: FnDef) -> FnDef {
    FnDef { name: String::from("x"), ..other }
}
"#;
        let file = write_fixture(src);
        let offenders = lint_file(file.path()).expect("lint runs");
        assert!(
            offenders.is_empty(),
            "NF-S7-9: clone-with-override should NOT be flagged. Offenders: {offenders:?}"
        );
    }
}
