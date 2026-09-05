//! The durable scheduler: fixed-interval entries whose last-run marks
//! persist to disk, so a restarted host resumes the cadence instead of
//! starting over.
//!
//! Semantics, chosen for one-shot tools:
//! - an entry that has NEVER run fires immediately at boot;
//! - an entry that is overdue (host was down past its deadline) fires
//!   ONCE, not once per missed interval — no backfill storms;
//! - the mark is persisted (atomic tmp + rename, the kv pattern)
//!   after every run, so a crash between runs loses at most "this run
//!   already happened", which resolves to one early re-run, never a
//!   silent skip... the failure mode a durable scheduler must not
//!   have.
//!
//! Marks are wall-clock epoch milliseconds — restart durability is
//! the point, and only the wall clock survives a restart. Large NTP
//! steps therefore shift cadence; acceptable for v1 and documented.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::{Condvar, Mutex};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

use anyhow::Context;
use serde::{Deserialize, Serialize};

use crate::config::ScheduleEntry;
use crate::cron::{CronSpec, next_fire_after};
use crate::host::{ToolHost, ToolOutcome};

/// A schedule entry's cadence, resolved once at scheduler start.
enum Cadence {
    /// Fixed interval. Never-ran fires immediately at boot; the next
    /// run is `last + every_ms`; overdue fires once.
    Interval(u64),
    /// Cron slots (UTC). Never-ran does NOT fire at boot — the first
    /// run is the next slot after boot; after that, an entry whose
    /// next slot passed while the host was down fires ONCE.
    Cron(CronSpec),
}

impl Cadence {
    fn resolve(entry: &ScheduleEntry) -> Self {
        match (&entry.every_ms, &entry.cron) {
            (Some(every_ms), None) => Cadence::Interval(*every_ms),
            (None, Some(expr)) => {
                Cadence::Cron(crate::cron::parse(expr).expect("validated at config load"))
            }
            _ => unreachable!("config validation enforces exactly one cadence"),
        }
    }

    /// When this entry is next due, given its durable mark and the
    /// scheduler's boot time. `None` = never (unsatisfiable cron).
    fn due_at(&self, last_run_ms: Option<u64>, boot_ms: u64) -> Option<u64> {
        match self {
            Cadence::Interval(every_ms) => {
                Some(last_run_ms.map_or(boot_ms, |last| last.saturating_add(*every_ms)))
            }
            Cadence::Cron(spec) => next_fire_after(spec, last_run_ms.unwrap_or(boot_ms)),
        }
    }
}

const STATE_FILE: &str = "schedule_state.json";

#[derive(Debug, Default, Serialize, Deserialize)]
struct ScheduleState {
    /// Entry name → epoch ms of the last completed run.
    last_run_ms: BTreeMap<String, u64>,
}

fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

fn state_path(state_dir: &Path) -> PathBuf {
    state_dir.join(STATE_FILE)
}

fn load_state(state_dir: &Path) -> anyhow::Result<ScheduleState> {
    let path = state_path(state_dir);
    match std::fs::read_to_string(&path) {
        Ok(text) => serde_json::from_str(&text)
            .with_context(|| format!("corrupt scheduler state `{}`", path.display())),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(ScheduleState::default()),
        Err(e) => Err(e).with_context(|| format!("failed to read `{}`", path.display())),
    }
}

fn persist_state(state_dir: &Path, state: &ScheduleState) -> anyhow::Result<()> {
    let path = state_path(state_dir);
    let tmp = path.with_extension("json.tmp");
    let text = serde_json::to_string_pretty(state).context("serialize scheduler state")?;
    std::fs::write(&tmp, text).with_context(|| format!("write `{}`", tmp.display()))?;
    std::fs::rename(&tmp, &path).with_context(|| format!("rename onto `{}`", path.display()))?;
    Ok(())
}

/// A running scheduler. Call [`Scheduler::shutdown`] to stop it; the
/// current tool run (if any) completes first.
pub struct Scheduler {
    stop: Arc<(Mutex<bool>, Condvar)>,
    thread: Option<std::thread::JoinHandle<()>>,
}

impl Scheduler {
    pub fn shutdown(mut self) {
        let (lock, condvar) = &*self.stop;
        *lock.lock().expect("scheduler stop lock") = true;
        condvar.notify_all();
        if let Some(handle) = self.thread.take() {
            let _ = handle.join();
        }
    }
}

/// Run one entry immediately (a manual poke). Does NOT touch the
/// durable marks — a manual run must not shift the cadence.
pub fn run_once(entry: &ScheduleEntry, host: &ToolHost) -> ToolOutcome {
    host.execute(&entry.tool, entry.input.as_bytes())
}

pub fn start(
    entries: Vec<ScheduleEntry>,
    host: Arc<ToolHost>,
    state_dir: &Path,
) -> anyhow::Result<Scheduler> {
    std::fs::create_dir_all(state_dir)
        .with_context(|| format!("failed to create state dir `{}`", state_dir.display()))?;
    let mut state = load_state(state_dir)?;
    let state_dir = state_dir.to_path_buf();
    let boot_ms = now_ms();
    let cadences: Vec<Cadence> = entries.iter().map(Cadence::resolve).collect();
    let stop: Arc<(Mutex<bool>, Condvar)> = Arc::new((Mutex::new(false), Condvar::new()));

    let thread_stop = Arc::clone(&stop);
    let thread = std::thread::Builder::new()
        .name("sigil-serve-scheduler".to_owned())
        .spawn(move || {
            loop {
                let now = now_ms();

                // Run everything due; collect the nearest future deadline.
                let mut next_deadline: Option<u64> = None;
                for (entry, cadence) in entries.iter().zip(&cadences) {
                    let last = state.last_run_ms.get(&entry.name).copied();
                    let Some(due_at) = cadence.due_at(last, boot_ms) else {
                        continue; // unsatisfiable cron: never due
                    };
                    if due_at <= now {
                        run_entry(entry, &host);
                        state.last_run_ms.insert(entry.name.clone(), now_ms());
                        if let Err(e) = persist_state(&state_dir, &state) {
                            eprintln!("[sched] WARNING: failed to persist state: {e:#}");
                        }
                        let last = state.last_run_ms.get(&entry.name).copied();
                        if let Some(after) = cadence.due_at(last, boot_ms) {
                            next_deadline = Some(next_deadline.map_or(after, |d| d.min(after)));
                        }
                    } else {
                        next_deadline = Some(next_deadline.map_or(due_at, |d| d.min(due_at)));
                    }
                }

                // Sleep until the nearest deadline (or stop signal).
                let now = now_ms();
                let sleep_ms = next_deadline
                    .map_or(1_000, |deadline| deadline.saturating_sub(now))
                    .clamp(1, 60_000);
                let (lock, condvar) = &*thread_stop;
                let guard = lock.lock().expect("scheduler stop lock");
                if *guard {
                    break;
                }
                let (guard, _timeout) = condvar
                    .wait_timeout(guard, Duration::from_millis(sleep_ms))
                    .expect("scheduler condvar wait");
                if *guard {
                    break;
                }
            }
        })
        .context("failed to spawn scheduler thread")?;

    Ok(Scheduler {
        stop,
        thread: Some(thread),
    })
}

fn run_entry(entry: &ScheduleEntry, host: &ToolHost) {
    match host.execute(&entry.tool, entry.input.as_bytes()) {
        ToolOutcome::Success(output) => {
            println!(
                "[sched] {} ran `{}` ok ({} bytes: {})",
                entry.name,
                entry.tool,
                output.len(),
                preview(&output)
            );
        }
        ToolOutcome::ToolError(code) => {
            eprintln!(
                "[sched] {} ran `{}`: tool error {code}",
                entry.name, entry.tool
            );
        }
        ToolOutcome::HostError(message) => {
            eprintln!("[sched] {} ran `{}`: {message}", entry.name, entry.tool);
        }
    }
}

fn preview(bytes: &[u8]) -> String {
    let text: String = String::from_utf8_lossy(&bytes[..bytes.len().min(40)]).into_owned();
    text.chars()
        .map(|c| if c.is_control() { '.' } else { c })
        .collect()
}
