//! The registry verbs (add/search/list) over `sigil-registry`'s local
//! SQLite template store — resolved to `sigil_templates.db` in the
//! working directory unless `$SIGIL_REGISTRY` overrides — plus the
//! store-opening helper `forge` shares.

use std::env;
use std::path::PathBuf;

use anyhow::bail;
use serde_json::json;
use sigil_compiler::{
    CompileLimits, CompilerContext, compile_tool_with_limits_and_context, source::SourceFile,
};
use sigil_registry::{TemplateRecord, TemplateStore};

use crate::json_envelope::{Envelope, OutputFormat, compile_error_to_json};

use crate::args::{CommandKind, RegistryAddCommand, RegistrySearchCommand};

// ---------------------------------------------------------------------------
// Registry helpers
// ---------------------------------------------------------------------------

fn registry_path() -> PathBuf {
    if let Ok(path) = env::var("SIGIL_REGISTRY") {
        return PathBuf::from(path);
    }
    PathBuf::from("sigil_templates.db")
}

pub(crate) fn open_registry() -> anyhow::Result<TemplateStore> {
    let path = registry_path();
    TemplateStore::open(&path)
        .map_err(|e| anyhow::anyhow!("failed to open registry at {}: {e}", path.display()))
}

// ---------------------------------------------------------------------------
// Registry commands
// ---------------------------------------------------------------------------

pub(crate) fn run_registry_add(
    command: &RegistryAddCommand,
    fmt: OutputFormat,
    context: &CompilerContext,
) -> anyhow::Result<()> {
    // P2: same tool-source cap as `forge` — the registry must not accept an
    // oversized source either.
    let compile_result = match compile_tool_with_limits_and_context(
        &command.source_text,
        &CompileLimits::default(),
        context,
    ) {
        Ok(result) => result,
        Err(err) => {
            let source = SourceFile::new(command.source_name.clone(), command.source_text.clone());
            if fmt.is_json() {
                let diags = compile_error_to_json(&err, &source);
                Envelope::error(CommandKind::RegistryAdd.json_name(), diags).emit();
                bail!("registry add: source failed compilation");
            }
            let rendered = err
                .diagnostics()
                .iter()
                .map(|diagnostic| diagnostic.render(&source))
                .collect::<Vec<_>>()
                .join("\n\n");
            bail!("Source failed compilation:\n{rendered}");
        }
    };

    let store = open_registry()?;
    let record = TemplateRecord {
        id: 0,
        task_description: command.task_desc.clone(),
        effect_row: String::new(),
        source: command.source_text.clone(),
        signature: format!(
            "fn tool_main() [wasm {} bytes, {} fns]",
            compile_result.wasm.len(),
            compile_result.function_count,
        ),
        ast_node_count: 0,
        fuel_consumed: None,
        created_at: now_iso8601(),
        tags: command.tags.clone(),
    };

    let id = store
        .add(&record)
        .map_err(|e| anyhow::anyhow!("failed to add template: {e}"))?;

    if fmt.is_json() {
        let data = json!({
            "template_id": id,
            "task_description": command.task_desc,
            "tags": command.tags,
        });
        Envelope::ok(CommandKind::RegistryAdd.json_name(), data).emit();
    } else {
        println!("Added template #{id}: {}", command.task_desc);
    }
    Ok(())
}

pub(crate) fn run_registry_search(
    command: &RegistrySearchCommand,
    fmt: OutputFormat,
) -> anyhow::Result<()> {
    let store = open_registry()?;
    let results = store
        .search(&command.query, 20)
        .map_err(|e| anyhow::anyhow!("search failed: {e}"))?;

    if fmt.is_json() {
        let json_results: Vec<serde_json::Value> = results.iter().map(template_to_json).collect();
        let data = json!({
            "query": command.query,
            "results": json_results,
        });
        Envelope::ok(CommandKind::RegistrySearch.json_name(), data).emit();
        return Ok(());
    }

    if results.is_empty() {
        println!("No templates found matching \"{}\".", command.query);
    } else {
        println!("Found {} template(s):", results.len());
        for r in &results {
            print_template_summary(r);
        }
    }
    Ok(())
}

pub(crate) fn run_registry_list(fmt: OutputFormat) -> anyhow::Result<()> {
    let store = open_registry()?;
    let results = store
        .list(100)
        .map_err(|e| anyhow::anyhow!("list failed: {e}"))?;

    if fmt.is_json() {
        let json_results: Vec<serde_json::Value> = results.iter().map(template_to_json).collect();
        let data = json!({
            "results": json_results,
        });
        Envelope::ok(CommandKind::RegistryList.json_name(), data).emit();
        return Ok(());
    }

    if results.is_empty() {
        println!("Registry is empty.");
    } else {
        println!("{} template(s) in registry:", results.len());
        for r in &results {
            print_template_summary(r);
        }
    }
    Ok(())
}

fn template_to_json(r: &TemplateRecord) -> serde_json::Value {
    json!({
        "id": r.id,
        "task_description": r.task_description,
        "tags": r.tags,
        "fuel_consumed": r.fuel_consumed,
        "signature": r.signature,
        "created_at": r.created_at,
    })
}

fn print_template_summary(r: &TemplateRecord) {
    let tags = r.tags.join(", ");
    let fuel = r
        .fuel_consumed
        .map(|f| f.to_string())
        .unwrap_or_else(|| "-".to_owned());
    println!(
        "  #{}: {} [tags: {}] [fuel: {}]",
        r.id, r.task_description, tags, fuel
    );
}

fn now_iso8601() -> String {
    use std::time::{SystemTime, UNIX_EPOCH};
    let secs = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs();
    let days = secs / 86400;
    let time_of_day = secs % 86400;
    let hours = time_of_day / 3600;
    let minutes = (time_of_day % 3600) / 60;
    let seconds = time_of_day % 60;

    let (year, month, day) = days_to_ymd(days);
    format!("{year:04}-{month:02}-{day:02}T{hours:02}:{minutes:02}:{seconds:02}Z")
}

fn days_to_ymd(days: u64) -> (u64, u64, u64) {
    let z = days as i64 + 719468;
    let era = if z >= 0 { z } else { z - 146096 } / 146097;
    let doe = (z - era * 146097) as u64;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe as i64 + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    (y as u64, m, d)
}
