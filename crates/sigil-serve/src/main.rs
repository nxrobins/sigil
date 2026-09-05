//! sigil-serve — run SIGIL tools behind an HTTP trigger and a durable
//! scheduler.
//!
//! Usage:
//!   sigil-serve <config.json>            start the configured service
//!   sigil-serve <config.json> --check    validate config + compile tools, then exit
//!   sigil-serve <config.json> --once <entry>
//!                                        run one schedule entry now and exit
//!                                        (does not touch durable marks)

use std::path::Path;
use std::sync::Arc;

use anyhow::bail;
use sigil_serve::config::Config;
use sigil_serve::host::{ToolHost, ToolOutcome};
use sigil_serve::{http, scheduler};

fn main() {
    if let Err(e) = run() {
        eprintln!("error: {e:#}");
        std::process::exit(1);
    }
}

fn run() -> anyhow::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    let Some(config_path) = args.get(1).filter(|a| !a.starts_with("--")) else {
        bail!("usage: sigil-serve <config.json> [--check | --once <entry>]");
    };

    let mut check_only = false;
    let mut once_entry: Option<String> = None;
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--check" => check_only = true,
            "--once" => {
                i += 1;
                let Some(name) = args.get(i) else {
                    bail!("--once requires a schedule entry name");
                };
                once_entry = Some(name.clone());
            }
            other => bail!("unknown flag `{other}`"),
        }
        i += 1;
    }

    let (config, base_dir) = Config::load(Path::new(config_path))?;
    let host = Arc::new(ToolHost::from_config(&config, &base_dir)?);

    if check_only {
        let tools: Vec<&str> = host.tool_names().collect();
        println!(
            "config ok: {} tool(s) compiled ({}), {} route(s), {} schedule entrie(s)",
            tools.len(),
            tools.join(", "),
            config.http.as_ref().map_or(0, |h| h.routes.len()),
            config.schedule.len()
        );
        return Ok(());
    }

    if let Some(name) = once_entry {
        let Some(entry) = config.schedule.iter().find(|e| e.name == name) else {
            bail!("no schedule entry named `{name}`");
        };
        return match scheduler::run_once(entry, &host) {
            ToolOutcome::Success(output) => {
                println!("{}", String::from_utf8_lossy(&output));
                Ok(())
            }
            ToolOutcome::ToolError(code) => bail!("tool error {code}"),
            ToolOutcome::HostError(message) => bail!("{message}"),
        };
    }

    let _http_server = match &config.http {
        Some(http_config) => {
            let server = http::start(http_config, Arc::clone(&host))?;
            println!("[serve] http listening on {}", server.bound);
            for route in &http_config.routes {
                println!("[serve]   {} -> tool `{}`", route.path, route.tool);
            }
            Some(server)
        }
        None => None,
    };

    let _sched = if config.schedule.is_empty() {
        None
    } else {
        let state_dir = config
            .state_dir
            .as_ref()
            .expect("validated: schedule requires state_dir");
        let state_dir = if state_dir.is_absolute() {
            state_dir.clone()
        } else {
            base_dir.join(state_dir)
        };
        for entry in &config.schedule {
            let cadence = match (&entry.every_ms, &entry.cron) {
                (Some(ms), _) => format!("every {ms} ms"),
                (_, Some(expr)) => format!("cron `{expr}` (UTC)"),
                _ => unreachable!("validated"),
            };
            println!(
                "[serve] schedule `{}` -> tool `{}` {}",
                entry.name, entry.tool, cadence
            );
        }
        Some(scheduler::start(
            config.schedule.clone(),
            Arc::clone(&host),
            &state_dir,
        )?)
    };

    // Serve until killed. (Graceful signal handling without new
    // dependencies is a follow-up; the durable scheduler makes an
    // abrupt exit safe — at worst one entry re-runs early.)
    loop {
        std::thread::park();
    }
}
