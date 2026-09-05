//! Compile throughput bench (one-shot, doc-published).
//!
//! Walks the three test corpora — `tests/fixtures/`,
//! `tests/cve_corpus/*.sigil`, `tests/z3_corpus/` — and records per-
//! fixture compile latency with coefficient-of-variation (CV)
//! convergence. Per the v2 plan (citation pre-flight, MC-3, MI-1,
//! UP-3 fences): runs until CV<5% over the trailing 30-sample
//! window OR sample count hits 500.
//!
//! Two columns are published side-by-side; this binary is meant to
//! be run twice:
//!
//!     cargo run --release --example throughput                              # default features (solver + json)
//!     cargo run --release --example throughput --no-default-features --features json
//!
//! The first run includes Z3 capability proofs; the second skips
//! them. Per UP-1/UP-2, we do NOT publish "Z3 cost = delta" as a
//! headline — we publish both columns and let the reader subtract.
//!
//! Output is a markdown table to stdout. Authors paste the output
//! into PERFORMANCE.md.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use sigil_compiler::compile_named_module;

const WARMUP_RUNS: usize = 1;
const MIN_SAMPLES: usize = 30;
const MAX_SAMPLES: usize = 500;
const CV_CONVERGED: f64 = 5.0; // %
const CV_DROP_FROM_TOTALS: f64 = 20.0; // %

#[derive(Debug, Clone)]
struct FixtureStat {
    name: String,
    n: usize,
    median_us: u128,
    p90_us: u128,
    max_us: u128,
    cv_pct: f64,
}

impl FixtureStat {
    fn flag(&self) -> &'static str {
        if self.cv_pct < CV_CONVERGED {
            "✓"
        } else if self.cv_pct < CV_DROP_FROM_TOTALS {
            "⚠"
        } else {
            "✗"
        }
    }
    fn in_totals(&self) -> bool {
        self.cv_pct < CV_DROP_FROM_TOTALS
    }
}

#[derive(Debug)]
struct CorpusReport {
    name: String,
    files_measured: usize,
    files_dropped: usize,
    median_us: u128,
    p90_us: u128,
    total_us: u128,
    per_file: Vec<FixtureStat>,
}

fn manifest_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn corpus_paths() -> Vec<(String, PathBuf)> {
    let base = manifest_dir().join("tests");
    vec![
        ("fixtures".to_string(), base.join("fixtures")),
        ("cve_corpus".to_string(), base.join("cve_corpus")),
        ("z3_corpus".to_string(), base.join("z3_corpus")),
    ]
}

fn collect_sigil_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    if !dir.is_dir() {
        return out;
    }
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return out,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("sigil") {
            out.push(path);
        }
    }
    out.sort();
    out
}

fn percentile(sorted: &[u128], pct: f64) -> u128 {
    if sorted.is_empty() {
        return 0;
    }
    let idx = ((sorted.len() as f64 - 1.0) * pct / 100.0).round() as usize;
    sorted[idx.min(sorted.len() - 1)]
}

fn mean(samples: &[u128]) -> f64 {
    let sum: u128 = samples.iter().sum();
    sum as f64 / samples.len() as f64
}

fn stddev(samples: &[u128], mean_val: f64) -> f64 {
    if samples.len() < 2 {
        return 0.0;
    }
    let var: f64 = samples
        .iter()
        .map(|&x| {
            let d = x as f64 - mean_val;
            d * d
        })
        .sum::<f64>()
        / (samples.len() - 1) as f64;
    var.sqrt()
}

fn cv_pct(samples: &[u128]) -> f64 {
    let m = mean(samples);
    if m == 0.0 {
        return 0.0;
    }
    stddev(samples, m) / m * 100.0
}

fn time_one_compile(name: &str, source: &str) -> Duration {
    let start = Instant::now();
    let _ = compile_named_module(name, source);
    start.elapsed()
}

fn measure_fixture(path: &Path) -> FixtureStat {
    let name = path
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or("?")
        .to_string();
    let source = match fs::read_to_string(path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("warning: failed to read {}: {e}", path.display());
            return FixtureStat {
                name,
                n: 0,
                median_us: 0,
                p90_us: 0,
                max_us: 0,
                cv_pct: 0.0,
            };
        }
    };

    for _ in 0..WARMUP_RUNS {
        let _ = time_one_compile(&name, &source);
    }

    let mut samples: Vec<u128> = Vec::with_capacity(MIN_SAMPLES);
    while samples.len() < MAX_SAMPLES {
        let d = time_one_compile(&name, &source);
        samples.push(d.as_micros());
        if samples.len() >= MIN_SAMPLES {
            let trailing = &samples[samples.len() - MIN_SAMPLES..];
            if cv_pct(trailing) < CV_CONVERGED {
                break;
            }
        }
    }

    let mut sorted = samples.clone();
    sorted.sort_unstable();
    FixtureStat {
        name,
        n: samples.len(),
        median_us: percentile(&sorted, 50.0),
        p90_us: percentile(&sorted, 90.0),
        max_us: *sorted.last().unwrap_or(&0),
        cv_pct: cv_pct(&samples),
    }
}

fn measure_corpus(name: &str, dir: &Path) -> CorpusReport {
    let files = collect_sigil_files(dir);
    let mut per_file = Vec::with_capacity(files.len());
    for path in &files {
        per_file.push(measure_fixture(path));
    }

    let in_totals: Vec<&FixtureStat> = per_file.iter().filter(|s| s.in_totals()).collect();
    let mut medians: Vec<u128> = in_totals.iter().map(|s| s.median_us).collect();
    medians.sort_unstable();
    let mut p90s: Vec<u128> = in_totals.iter().map(|s| s.p90_us).collect();
    p90s.sort_unstable();

    CorpusReport {
        name: name.to_string(),
        files_measured: in_totals.len(),
        files_dropped: per_file.len() - in_totals.len(),
        median_us: percentile(&medians, 50.0),
        p90_us: percentile(&p90s, 90.0),
        total_us: in_totals.iter().map(|s| s.median_us).sum(),
        per_file,
    }
}

fn print_markdown(reports: &[CorpusReport]) {
    let solver_on = cfg!(feature = "solver");
    let label = if solver_on { "solver=ON" } else { "solver=OFF" };

    println!("# Compile throughput — {label}");
    println!();
    println!(
        "Convergence: per-fixture sample count is bounded above by {MAX_SAMPLES}, \
         minimum {MIN_SAMPLES}, terminates when trailing CV < {CV_CONVERGED:.1}%."
    );
    println!(
        "Fixtures with CV ≥ {CV_DROP_FROM_TOTALS:.0}% are dropped from per-corpus medians/totals (✗ flag)."
    );
    println!();

    println!("## Per-corpus summary ({label})");
    println!();
    println!(
        "| Corpus | Files measured | Dropped (CV>{CV_DROP_FROM_TOTALS:.0}%) | Median (μs) | P90 (μs) | Total (μs) |"
    );
    println!("|---|---:|---:|---:|---:|---:|");
    for r in reports {
        println!(
            "| {} | {} | {} | {} | {} | {} |",
            r.name, r.files_measured, r.files_dropped, r.median_us, r.p90_us, r.total_us
        );
    }
    println!();

    for r in reports {
        println!("## {} — per-fixture detail ({label})", r.name);
        println!();
        println!("| Fixture | n | Median (μs) | P90 (μs) | Max (μs) | CV % | Flag |");
        println!("|---|---:|---:|---:|---:|---:|:-:|");
        for s in &r.per_file {
            println!(
                "| {} | {} | {} | {} | {} | {:.1} | {} |",
                s.name,
                s.n,
                s.median_us,
                s.p90_us,
                s.max_us,
                s.cv_pct,
                s.flag(),
            );
        }
        println!();
    }
}

fn main() {
    let reports: Vec<CorpusReport> = corpus_paths()
        .into_iter()
        .map(|(name, dir)| measure_corpus(&name, &dir))
        .collect();
    print_markdown(&reports);
}
