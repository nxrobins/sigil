//! Source fence for the walker blind-spot class (F005 — the recurring
//! "structural walker forgot an arm" defect: PRs #29, #89, #343, #418, #463).
//!
//! The primary defense is compile-time: every security-relevant `Type`
//! walker is a TOTAL match (no `_` arm), so a new `Type` variant fails to
//! compile until each walker classifies it. Each walker is pinned with
//! `#[deny(clippy::wildcard_enum_match_arm)]` so a wildcard can't come back
//! without tripping the CI clippy gate (`-D warnings`).
//!
//! THIS test pins the pin: deleting one of those attributes (which would
//! silently re-open the wildcard path) fails here until the census below is
//! deliberately edited. Feature-INDEPENDENT pure source scan — house
//! pattern: z3_guard_fences.rs.

use std::fs;
use std::path::{Path, PathBuf};

fn compiler_src() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
}

/// (file, walker fn name) pairs that MUST carry the deny attribute.
/// Adding a new security walker (any `Type` walker whose verdict feeds an
/// accept/reject decision)? Add it here AND give it a total match — see the
/// fn docs on `type_contains_cap` for the classification rules.
const FENCED_WALKERS: &[(&str, &str)] = &[
    ("type_check/resolve.rs", "type_contains_cap"),
    ("type_check/resolve.rs", "type_contains_never"),
    ("type_check/resolve.rs", "type_contains_typestate"),
    ("type_check/resolve.rs", "type_contains_wide_int"),
    ("type_check/resolve.rs", "type_is_reassignable"),
    ("ring_check.rs", "is_owned_cap"),
    ("ring_check.rs", "contains_cap_ref"),
];

const DENY_ATTR: &str = "#[deny(clippy::wildcard_enum_match_arm)]";

/// True if `line` is the DEFINITION line of `name` (not a call site or a
/// prose mention in a doc comment).
fn is_fn_def(line: &str, name: &str) -> bool {
    let t = line.trim_start();
    t.starts_with(&format!("fn {name}(")) || t.starts_with(&format!("pub(super) fn {name}("))
}

#[test]
fn every_security_walker_carries_the_wildcard_deny_attribute() {
    for (file, name) in FENCED_WALKERS {
        let path = compiler_src().join(file);
        let src = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let lines: Vec<&str> = src.lines().collect();
        let fn_line = lines
            .iter()
            .position(|l| is_fn_def(l, name))
            .unwrap_or_else(|| {
                panic!(
                    "`fn {name}` not found in {file} — if the walker moved or was \
                     renamed, update FENCED_WALKERS in walker_fence.rs"
                )
            });
        let attr_present = lines[fn_line.saturating_sub(2)..fn_line]
            .iter()
            .any(|l| l.trim() == DENY_ATTR);
        assert!(
            attr_present,
            "{file}: `fn {name}` must be immediately preceded by `{DENY_ATTR}` — \
             the walker blind-spot fence (F005). A wildcard arm in a security \
             walker is exactly how the T183/T184/T186/T242 cap-smuggling class \
             regressed; if you believe this walker no longer needs the fence, \
             edit FENCED_WALKERS deliberately and say why in the PR."
        );
    }
}

/// The walkers' matches must stay TOTAL: no wildcard arm inside any fenced
/// walker's body. (Clippy enforces this too via the deny attribute; this
/// text-level check also fires in `cargo test` where clippy doesn't run,
/// and catches a `#[allow]` sneaked between the deny and the match.)
#[test]
fn fenced_walker_bodies_have_no_wildcard_arm() {
    for (file, name) in FENCED_WALKERS {
        let path = compiler_src().join(file);
        let src = fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
        let lines: Vec<&str> = src.lines().collect();
        let fn_line = lines
            .iter()
            .position(|l| is_fn_def(l, name))
            .expect("definition located by the sibling test");
        // Walk the fn body by brace depth from the definition line.
        let mut depth = 0i32;
        let mut entered = false;
        for (off, line) in lines[fn_line..].iter().enumerate() {
            for ch in line.chars() {
                match ch {
                    '{' => {
                        depth += 1;
                        entered = true;
                    }
                    '}' => depth -= 1,
                    _ => {}
                }
            }
            let code = line.split("//").next().unwrap_or("").trim();
            assert!(
                !(code.starts_with("_ =>")
                    || code.contains("#[allow(clippy::wildcard_enum_match_arm)]")),
                "{file}: `fn {name}` line {} re-opens the wildcard path — the \
                 walker blind-spot fence (F005) requires a TOTAL match; classify \
                 the variant explicitly instead",
                fn_line + off + 1,
            );
            if entered && depth == 0 {
                break;
            }
        }
    }
}
