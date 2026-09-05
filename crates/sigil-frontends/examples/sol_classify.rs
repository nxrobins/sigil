//! SOL-MEASURE — thin Solidity-frontend coverage classifier (frontier #6, "measure first").
//!
//! Runs the CURRENT Solidity frontend over a directory of real verified `.sol` contracts and
//! prints a frequency-sorted histogram of outcomes (OK / `FE####` reject / PANIC / TIMEOUT /
//! READ_ERR) plus the overall translate-rate. The point is to MEASURE the real-world reject
//! distribution empirically so the next frontier is chosen from data, not intuition.
//!
//! Usage: `cargo run -p sigil-frontends --example sol_classify -- [CORPUS_DIR] [--examples N]`
//! (CORPUS_DIR defaults to `corpus`). Every `translate` runs under `catch_unwind` + a per-file
//! timeout thread so one pathological contract cannot crash or hang the sweep — a PANIC/TIMEOUT
//! bucket is itself a finding (a frontend totality bug to fix).

use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::time::Duration;

use sigil_frontends::frontend_for;

const PER_FILE_TIMEOUT: Duration = Duration::from_secs(15);

fn main() {
    let mut args = std::env::args().skip(1);
    let mut dir = String::from("corpus");
    let mut examples = 3usize;
    while let Some(a) = args.next() {
        match a.as_str() {
            "--examples" => examples = args.next().and_then(|n| n.parse().ok()).unwrap_or(3),
            other => dir = other.to_string(),
        }
    }

    let mut files = Vec::new();
    collect_sol(Path::new(&dir), &mut files);
    files.sort();
    if files.is_empty() {
        eprintln!("no .sol files under {dir:?} — populate the corpus first");
        std::process::exit(2);
    }

    // bucket -> sample paths (we keep all for counts, show a few)
    let mut buckets: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for path in &files {
        let outcome = match std::fs::read_to_string(path) {
            Ok(src) => classify(&src, &path.display().to_string()),
            Err(_) => "READ_ERR".to_string(),
        };
        buckets
            .entry(outcome)
            .or_default()
            .push(path.display().to_string());
    }

    let total = files.len();
    let ok = buckets.get("OK").map(|v| v.len()).unwrap_or(0);

    // Sort buckets by count descending, then name.
    let mut rows: Vec<(&String, &Vec<String>)> = buckets.iter().collect();
    rows.sort_by(|a, b| b.1.len().cmp(&a.1.len()).then(a.0.cmp(b.0)));

    println!("\n=== SOL-MEASURE: {total} contracts under {dir:?} ===\n");
    println!(" count     pct  bucket");
    println!("------  ------  ------------------------");
    for (bucket, paths) in &rows {
        let pct = 100.0 * paths.len() as f64 / total as f64;
        println!("{:>6}  {:>5.1}%  {}", paths.len(), pct, bucket);
        for ex in paths.iter().take(examples) {
            println!("                  └─ {ex}");
        }
    }
    println!(
        "\ntranslate-rate: {ok}/{total} = {:.1}% OK\n",
        100.0 * ok as f64 / total as f64
    );
}

/// Classify ONE contract: OK / the first diagnostic's FE-code / PANIC (caught) / TIMEOUT.
/// Runs `translate` on a worker thread so a hang is bounded by `PER_FILE_TIMEOUT` (the thread
/// is then abandoned — sound for a measurement tool; the frontend's depth guards make a true
/// hang unlikely, so TIMEOUT itself flags a totality bug).
fn classify(src: &str, name: &str) -> String {
    let (tx, rx) = mpsc::channel();
    let src = src.to_string();
    let name = name.to_string();
    std::thread::spawn(move || {
        let outcome = catch_unwind(AssertUnwindSafe(|| {
            match frontend_for("solidity")
                .expect("solidity registered")
                .translate(&src, &name)
            {
                Ok(_) => "OK".to_string(),
                Err(diags) => diags
                    .first()
                    .map(|d| format!("{}  {}", d.code, normalize_msg(&d.message)))
                    .unwrap_or_else(|| "ERR_EMPTY".to_string()),
            }
        }))
        .unwrap_or_else(|_| "PANIC".to_string());
        let _ = tx.send(outcome);
    });
    rx.recv_timeout(PER_FILE_TIMEOUT)
        .unwrap_or_else(|_| "TIMEOUT".to_string())
}

/// Normalize a diagnostic message so templated variants GROUP: backtick-quoted spans →
/// `` `…` ``, digit runs → `N`, truncated to 80 chars. Turns "type `Foo` is outside…" and
/// "type `Bar` is outside…" into one bucket so the FE401 catch-all becomes actionable.
fn normalize_msg(m: &str) -> String {
    let mut out = String::new();
    let mut in_tick = false;
    let mut last_digit = false;
    for ch in m.chars() {
        if ch == '`' {
            if !in_tick {
                out.push_str("`…`");
            }
            in_tick = !in_tick;
            last_digit = false;
            continue;
        }
        if in_tick {
            continue;
        }
        if ch.is_ascii_digit() {
            if !last_digit {
                out.push('N');
                last_digit = true;
            }
            continue;
        }
        last_digit = false;
        out.push(ch);
    }
    out.chars().take(80).collect()
}

/// Recursively collect `*.sol` files (bounded by the corpus; skips `target`/hidden dirs).
fn collect_sol(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in rd.flatten() {
        let p = entry.path();
        if p.is_dir() {
            let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
            if name != "target" && !name.starts_with('.') {
                collect_sol(&p, out);
            }
        } else if p.extension().and_then(|x| x.to_str()) == Some("sol") {
            out.push(p);
        }
    }
}
