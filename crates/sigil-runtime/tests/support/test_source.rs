use std::collections::HashSet;

/// Extract only real `#[test]` functions, never `fn` text inside a fixture string. Ignored tests
/// are INCLUDED — this answers "does the test exist", and an attribute between `#[test]` and `fn`
/// must never hide one.
pub fn test_fn_names_in(src: &str) -> HashSet<String> {
    scan_test_fns(src, false)
}

/// The `#[ignore]`d SUBSET of [`test_fn_names_in`]. An ignored test compiles, is found by every
/// name-based inventory, and never runs — so a claim naming one is proven by nothing while every
/// name check stays green. PIN-6 uses this to refuse such claims.
///
/// `allow(dead_code)`: this module is included by `#[path]` into several test binaries, each of
/// which uses a different subset. Only `claims_ledger` needs this one, and CI builds with
/// `-D warnings`.
#[allow(dead_code)]
pub fn ignored_test_fn_names_in(src: &str) -> HashSet<String> {
    scan_test_fns(src, true)
}

fn scan_test_fns(src: &str, only_ignored: bool) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut pending_test = false;
    let mut saw_ignore = false;
    for line in src.lines().map(str::trim_start) {
        if line.starts_with("#[test]") {
            pending_test = true;
            saw_ignore = false;
            continue;
        }
        if !pending_test {
            continue;
        }
        if line.starts_with("#[ignore") {
            saw_ignore = true;
            continue;
        }
        if line.is_empty() || line.starts_with("//") || line.starts_with("#[") {
            continue;
        }
        let function = line
            .strip_prefix("fn ")
            .or_else(|| line.strip_prefix("pub fn "))
            .or_else(|| line.strip_prefix("async fn "));
        if let Some(rest) = function {
            let end = rest
                .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .unwrap_or(rest.len());
            if end > 0 && (!only_ignored || saw_ignore) {
                names.insert(rest[..end].to_string());
            }
        }
        pending_test = false;
        saw_ignore = false;
    }
    names
}
