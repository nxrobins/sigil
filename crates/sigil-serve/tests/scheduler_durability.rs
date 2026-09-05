//! Durable-scheduler tests: cadence survives restarts, overdue entries
//! fire once (no backfill), manual runs don't shift the marks.

mod common;

use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use common::{COUNTER_TOOL, TempDir, json_escaped_path, read_counter, wait_until, write_service};
use sigil_serve::config::Config;
use sigil_serve::host::{ToolHost, ToolOutcome};
use sigil_serve::scheduler;

/// Build the counter service pieces with a given interval; returns
/// (config, host, state_dir, kv_dir).
fn counter_service(
    dir: &Path,
    every_ms: u64,
) -> (
    Config,
    Arc<ToolHost>,
    std::path::PathBuf,
    std::path::PathBuf,
) {
    let kv_dir = dir.join("kvdata");
    let state_dir = dir.join("state");
    std::fs::create_dir_all(&kv_dir).unwrap();
    let config_json = format!(
        r#"{{
  "host_profile": "ephemeral",
  "tools": {{ "counter": {{ "source": "counter.sigil", "grants": {{
    "kv": ["demo={kv}"], "kv_write": ["demo={kv}"] }} }} }},
  "schedule": [ {{ "name": "tick", "tool": "counter", "every_ms": {every_ms} }} ],
  "state_dir": "state"
}}"#,
        kv = json_escaped_path(&kv_dir)
    );
    let config_path = write_service(dir, &config_json, &[("counter.sigil", COUNTER_TOOL)]);
    let (config, base_dir) = Config::load(&config_path).expect("config loads");
    let host = Arc::new(ToolHost::from_config(&config, &base_dir).expect("compiles"));
    (config, host, state_dir, kv_dir)
}

#[test]
fn never_ran_fires_at_boot_then_ticks() {
    let dir = TempDir::new("sched_ticks");
    let (config, host, state_dir, kv_dir) = counter_service(dir.path(), 150);

    let sched = scheduler::start(config.schedule.clone(), host, &state_dir).expect("starts");
    // First run is immediate (never-ran == infinitely overdue), then
    // the interval takes over: expect the counter to reach 3+.
    assert!(
        wait_until(Duration::from_secs(10), || read_counter(&kv_dir)
            .is_some_and(|n| n >= 3)),
        "counter should tick at least 3 times, got {:?}",
        read_counter(&kv_dir)
    );
    sched.shutdown();

    // The durable mark exists and is fresh.
    let state_text =
        std::fs::read_to_string(state_dir.join("schedule_state.json")).expect("state persisted");
    assert!(
        state_text.contains("tick"),
        "state names the entry: {state_text}"
    );
}

#[test]
fn cadence_survives_restart_without_rerunning() {
    let dir = TempDir::new("sched_restart");
    // Interval far larger than the test: the only legitimate run is
    // the never-ran boot run.
    let (config, host, state_dir, kv_dir) = counter_service(dir.path(), 60_000);

    let sched =
        scheduler::start(config.schedule.clone(), Arc::clone(&host), &state_dir).expect("starts");
    assert!(
        wait_until(Duration::from_secs(10), || read_counter(&kv_dir) == Some(1)),
        "boot run should set counter to 1"
    );
    sched.shutdown();

    // Restart over the same state dir. Without a persisted mark this
    // would look never-ran and fire again; the mark must prevent that.
    let sched = scheduler::start(config.schedule.clone(), host, &state_dir).expect("restarts");
    std::thread::sleep(Duration::from_millis(500));
    assert_eq!(
        read_counter(&kv_dir),
        Some(1),
        "restart within the interval must NOT re-run the entry"
    );
    sched.shutdown();
}

#[test]
fn overdue_entry_fires_once_not_per_missed_interval() {
    let dir = TempDir::new("sched_overdue");
    let (config, host, state_dir, kv_dir) = counter_service(dir.path(), 5_000);

    // Boot run establishes counter = 1 and a mark.
    let sched =
        scheduler::start(config.schedule.clone(), Arc::clone(&host), &state_dir).expect("starts");
    assert!(wait_until(Duration::from_secs(10), || read_counter(
        &kv_dir
    ) == Some(1)));
    sched.shutdown();

    // Rewrite the mark to 100 intervals ago — a long outage.
    let state_path = state_dir.join("schedule_state.json");
    let text = std::fs::read_to_string(&state_path).unwrap();
    let mut state: serde_json::Value = serde_json::from_str(&text).unwrap();
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    state["last_run_ms"]["tick"] = serde_json::json!(now_ms - 500_000);
    std::fs::write(&state_path, serde_json::to_string(&state).unwrap()).unwrap();

    // Restart: exactly ONE catch-up run, not 100 backfills.
    let sched = scheduler::start(config.schedule.clone(), host, &state_dir).expect("restarts");
    assert!(
        wait_until(Duration::from_secs(10), || read_counter(&kv_dir) == Some(2)),
        "overdue entry should catch up once, got {:?}",
        read_counter(&kv_dir)
    );
    std::thread::sleep(Duration::from_millis(500));
    assert_eq!(
        read_counter(&kv_dir),
        Some(2),
        "no backfill: one catch-up run only"
    );
    sched.shutdown();
}

#[test]
fn run_once_executes_but_leaves_marks_alone() {
    let dir = TempDir::new("sched_once");
    let (config, host, state_dir, kv_dir) = counter_service(dir.path(), 60_000);

    let entry = &config.schedule[0];
    match scheduler::run_once(entry, &host) {
        ToolOutcome::Success(output) => {
            assert_eq!(String::from_utf8_lossy(&output), "1");
        }
        other => panic!("run_once should succeed, got {other:?}"),
    }
    assert_eq!(read_counter(&kv_dir), Some(1), "the tool really ran");
    assert!(
        !state_dir.join("schedule_state.json").exists(),
        "a manual poke must not create durable marks"
    );
}

/// Build the counter service with a CRON cadence instead of an interval.
fn cron_counter_service(
    dir: &Path,
    cron: &str,
) -> (
    Config,
    Arc<ToolHost>,
    std::path::PathBuf,
    std::path::PathBuf,
) {
    let kv_dir = dir.join("kvdata");
    let state_dir = dir.join("state");
    std::fs::create_dir_all(&kv_dir).unwrap();
    let config_json = format!(
        r#"{{
  "host_profile": "ephemeral",
  "tools": {{ "counter": {{ "source": "counter.sigil", "grants": {{
    "kv": ["demo={kv}"], "kv_write": ["demo={kv}"] }} }} }},
  "schedule": [ {{ "name": "tick", "tool": "counter", "cron": "{cron}" }} ],
  "state_dir": "state"
}}"#,
        kv = json_escaped_path(&kv_dir)
    );
    let config_path = write_service(dir, &config_json, &[("counter.sigil", COUNTER_TOOL)]);
    let (config, base_dir) = Config::load(&config_path).expect("config loads");
    let host = Arc::new(ToolHost::from_config(&config, &base_dir).expect("compiles"));
    (config, host, state_dir, kv_dir)
}

#[test]
fn cron_never_ran_does_not_fire_at_boot() {
    // Unlike intervals, a cron entry waits for its next slot — here
    // Jan 1 midnight, comfortably far from any test run.
    let dir = TempDir::new("cron_boot");
    let (config, host, state_dir, kv_dir) = cron_counter_service(dir.path(), "0 0 1 1 *");
    let sched = scheduler::start(config.schedule.clone(), host, &state_dir).expect("starts");
    std::thread::sleep(Duration::from_millis(400));
    assert_eq!(
        read_counter(&kv_dir),
        None,
        "cron entry must wait for its slot, not fire at boot"
    );
    sched.shutdown();
}

#[test]
fn cron_overdue_fires_exactly_once() {
    let dir = TempDir::new("cron_overdue");
    let (config, host, state_dir, kv_dir) = cron_counter_service(dir.path(), "* * * * *");

    // If the next minute boundary is imminent, wait it out so the
    // catch-up run and a legitimate next-slot run can't blur.
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let into_minute = now_ms % 60_000;
    if into_minute > 55_000 {
        std::thread::sleep(Duration::from_millis(6_000));
    }

    // Pre-seed a durable mark 10 minutes in the past — a host outage
    // spanning ten every-minute slots.
    std::fs::create_dir_all(&state_dir).unwrap();
    let now_ms = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as u64;
    let state = serde_json::json!({ "last_run_ms": { "tick": now_ms - 600_000 } });
    std::fs::write(
        state_dir.join("schedule_state.json"),
        serde_json::to_string(&state).unwrap(),
    )
    .unwrap();

    let sched = scheduler::start(config.schedule.clone(), host, &state_dir).expect("starts");
    assert!(
        wait_until(Duration::from_secs(10), || read_counter(&kv_dir) == Some(1)),
        "overdue cron entry should catch up once, got {:?}",
        read_counter(&kv_dir)
    );
    std::thread::sleep(Duration::from_millis(400));
    assert_eq!(
        read_counter(&kv_dir),
        Some(1),
        "ten missed slots must not backfill"
    );
    sched.shutdown();
}

#[test]
fn cron_config_validation() {
    let dir = TempDir::new("cron_config");
    std::fs::write(dir.path().join("c.sigil"), COUNTER_TOOL).unwrap();
    let cases: &[(&str, &str)] = &[
        (r#""cron": "not a cron""#, "expected 5 fields"),
        (r#""cron": "* * * * *", "every_ms": 1000"#, "not both"),
        (r#""#, "needs `every_ms` or `cron`"),
        (r#""cron": "61 * * * *""#, "outside"),
    ];
    for (cadence, fragment) in cases {
        let sep = if cadence.is_empty() { "" } else { ", " };
        let config = format!(
            r#"{{ "tools": {{ "c": {{ "source": "c.sigil" }} }},
                 "schedule": [ {{ "name": "t", "tool": "c"{sep}{cadence} }} ],
                 "state_dir": "state" }}"#
        );
        let path = dir.path().join("cfg.json");
        std::fs::write(&path, config).unwrap();
        let err = Config::load(&path).expect_err("must reject");
        assert!(
            format!("{err:#}").contains(fragment),
            "case {cadence:?}: expected `{fragment}` in {err:#}"
        );
    }
}
