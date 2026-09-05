//! The template registry — `sigil-cli`'s local SQLite store of tool templates
//! (`sigil registry add | search | list`).
//!
//! This crate is developer-workflow metadata, not part of the verified
//! pipeline: nothing here influences what the compiler accepts or what the
//! runtime grants. Its load-bearing constraints are durability-shaped:
//!
//! * **The schema is create-if-missing and append-only.** `ensure_schema`
//!   runs on every open against whatever file is already on disk, so a
//!   schema change must be additive (a new nullable column, a new table).
//!   Retyping or dropping a column would silently corrupt every existing
//!   per-user store — there is no migration machinery here on purpose;
//!   adding some is the trigger to revisit this header.
//! * **Ids are SQLite `AUTOINCREMENT` rowids**: assigned by the database,
//!   monotonically increasing, never reused. That makes an id a stable
//!   citation target for anything a user writes down.
//! * **Tags round-trip through a JSON array in a TEXT column**, written only
//!   by [`TemplateStore::add`]. The one deliberate fail-open seam in this
//!   crate is reading that column back — see the comment in
//!   [`row_to_record`] for the bound and the revisit trigger.
//!
//! Failure discipline: every fallible path returns [`RegistryError`] (typed,
//! `?`-propagated); there are no panicking paths in production code.

use std::fmt;
use std::path::Path;

use rusqlite::{Connection, params};

#[derive(Debug)]
pub enum RegistryError {
    Sqlite(rusqlite::Error),
    Json(serde_json::Error),
}

impl fmt::Display for RegistryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RegistryError::Sqlite(e) => write!(f, "sqlite error: {e}"),
            RegistryError::Json(e) => write!(f, "json error: {e}"),
        }
    }
}

impl std::error::Error for RegistryError {}

impl From<rusqlite::Error> for RegistryError {
    fn from(e: rusqlite::Error) -> Self {
        RegistryError::Sqlite(e)
    }
}

impl From<serde_json::Error> for RegistryError {
    fn from(e: serde_json::Error) -> Self {
        RegistryError::Json(e)
    }
}

#[derive(Debug, Clone)]
pub struct TemplateRecord {
    /// Database-assigned rowid. Ignored on [`TemplateStore::add`] (callers
    /// pass 0 by convention); authoritative everywhere else.
    pub id: u64,
    pub task_description: String,
    pub effect_row: String,
    pub source: String,
    pub signature: String,
    pub ast_node_count: u32,
    pub fuel_consumed: Option<u64>,
    pub created_at: String,
    pub tags: Vec<String>,
}

pub struct TemplateStore {
    db: Connection,
}

impl TemplateStore {
    /// Open (or create) the registry database at `path`, creating the schema
    /// if this is a fresh file. This is the CLI's entry point.
    pub fn open(path: &Path) -> Result<Self, RegistryError> {
        let db = Connection::open(path)?;
        let store = Self { db };
        store.ensure_schema()?;
        Ok(store)
    }

    /// Open a private in-memory database with the same schema. Test-only in
    /// practice: nothing persists past the connection.
    pub fn open_in_memory() -> Result<Self, RegistryError> {
        let db = Connection::open_in_memory()?;
        let store = Self { db };
        store.ensure_schema()?;
        Ok(store)
    }

    fn ensure_schema(&self) -> Result<(), RegistryError> {
        // Runs against pre-existing user stores on every open — additive
        // changes only (see the module header for why).
        self.db.execute_batch(
            "CREATE TABLE IF NOT EXISTS templates (
                id              INTEGER PRIMARY KEY AUTOINCREMENT,
                task_description TEXT NOT NULL,
                effect_row      TEXT NOT NULL,
                source          TEXT NOT NULL,
                signature       TEXT NOT NULL,
                ast_node_count  INTEGER NOT NULL,
                fuel_consumed   INTEGER,
                created_at      TEXT NOT NULL,
                tags            TEXT NOT NULL
            );",
        )?;
        Ok(())
    }

    /// Insert a template and return the database-assigned id (`record.id`
    /// is ignored — the rowid is the only id authority).
    pub fn add(&self, record: &TemplateRecord) -> Result<u64, RegistryError> {
        let tags_json = serde_json::to_string(&record.tags)?;
        self.db.execute(
            "INSERT INTO templates (task_description, effect_row, source, signature,
                                    ast_node_count, fuel_consumed, created_at, tags)
             VALUES (?1, ?2, ?3, ?4, ?5, ?6, ?7, ?8)",
            params![
                record.task_description,
                record.effect_row,
                record.source,
                record.signature,
                record.ast_node_count,
                record.fuel_consumed,
                record.created_at,
                tags_json,
            ],
        )?;
        // Rowids are positive by construction, so the sign cast is lossless.
        Ok(self.db.last_insert_rowid() as u64)
    }

    /// Retrieve a template by id; `None` if no such row.
    pub fn get(&self, id: u64) -> Result<Option<TemplateRecord>, RegistryError> {
        let mut stmt = self.db.prepare(
            "SELECT id, task_description, effect_row, source, signature,
                    ast_node_count, fuel_consumed, created_at, tags
             FROM templates WHERE id = ?1",
        )?;
        let mut rows = stmt.query_map(params![id], row_to_record)?;
        match rows.next() {
            Some(row) => Ok(Some(row?)),
            None => Ok(None),
        }
    }

    /// Substring search across `task_description`, `tags`, and `signature`,
    /// in that priority-free OR combination, capped at `limit` rows.
    ///
    /// Semantics a caller can observe: matching is SQL `LIKE` with the query
    /// wrapped in `%…%`, so it is case-insensitive for ASCII and the query's
    /// own `%`/`_` characters act as wildcards — they are deliberately NOT
    /// escaped (the consumer is a human at the CLI, and `sigil registry
    /// search 'http%get'` doing prefix-ish matching is a feature until
    /// someone needs literal percent signs in a tag). Tags are matched
    /// against the serialized JSON array, so a match may span tag
    /// boundaries.
    pub fn search(&self, query: &str, limit: usize) -> Result<Vec<TemplateRecord>, RegistryError> {
        let pattern = format!("%{query}%");
        let mut stmt = self.db.prepare(
            "SELECT id, task_description, effect_row, source, signature,
                    ast_node_count, fuel_consumed, created_at, tags
             FROM templates
             WHERE task_description LIKE ?1
                OR tags LIKE ?1
                OR signature LIKE ?1
             LIMIT ?2",
        )?;
        let rows = stmt.query_map(params![pattern, limit as u32], row_to_record)?;
        let mut results = Vec::new();
        for row in rows {
            results.push(row?);
        }
        Ok(results)
    }

    /// List templates in id (= insertion) order, capped at `limit` rows.
    pub fn list(&self, limit: usize) -> Result<Vec<TemplateRecord>, RegistryError> {
        let mut stmt = self.db.prepare(
            "SELECT id, task_description, effect_row, source, signature,
                    ast_node_count, fuel_consumed, created_at, tags
             FROM templates ORDER BY id LIMIT ?1",
        )?;
        let rows = stmt.query_map(params![limit as u32], row_to_record)?;
        let mut results = Vec::new();
        for row in rows {
            results.push(row?);
        }
        Ok(results)
    }

    /// Record a fuel measurement for a template.
    ///
    /// Updating an id with no matching row is a silent no-op (SQL `UPDATE`
    /// over zero rows succeeds) — a caller that needs existence confirmation
    /// must [`TemplateStore::get`] first. Stated rather than "fixed" because
    /// the only writer flow updates an id it just inserted.
    pub fn update_fuel(&self, id: u64, fuel: u64) -> Result<(), RegistryError> {
        self.db.execute(
            "UPDATE templates SET fuel_consumed = ?1 WHERE id = ?2",
            params![fuel, id],
        )?;
        Ok(())
    }

    /// Total number of templates in the store.
    pub fn count(&self) -> Result<u64, RegistryError> {
        let count: i64 = self
            .db
            .query_row("SELECT COUNT(*) FROM templates", [], |row| row.get(0))?;
        // COUNT(*) is non-negative, so the sign cast is lossless.
        Ok(count as u64)
    }

    /// Seed the built-in starter templates into an EMPTY store; any existing
    /// row (seeded or user-added) makes this a no-op. The guard keys on
    /// row count, not on seed presence — deleting the seeds and re-running
    /// does not resurrect them once the user has added anything.
    pub fn seed_defaults(&self) -> Result<(), RegistryError> {
        if self.count()? > 0 {
            return Ok(());
        }

        // Seed rows are deterministic fixtures: `created_at` is a fixed
        // epoch string, not wall clock, so two fresh stores are
        // byte-identical and the seeds are distinguishable from user
        // entries by timestamp.
        let defaults = [
            TemplateRecord {
                id: 0,
                task_description: "Echo input back unchanged".to_owned(),
                effect_row: String::new(),
                source: concat!(
                    "#[ring(outer)] module tool;\n",
                    "pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! {} {\n",
                    "    return 0;\n",
                    "}\n",
                )
                .to_owned(),
                signature: "fn tool_main(i32, i32) -> i64".to_owned(),
                ast_node_count: 4,
                fuel_consumed: None,
                created_at: "2025-01-01T00:00:00Z".to_owned(),
                tags: vec!["echo".to_owned(), "identity".to_owned(), "test".to_owned()],
            },
            TemplateRecord {
                id: 0,
                task_description: "Read a file from the filesystem".to_owned(),
                effect_row: "FsIO, Alloc".to_owned(),
                source: concat!(
                    "#[ring(outer)] module tool;\n",
                    "pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FsIO, Alloc } {\n",
                    "    return 0;\n",
                    "}\n",
                )
                .to_owned(),
                signature: "fn tool_main(i32, i32) -> i64".to_owned(),
                ast_node_count: 4,
                fuel_consumed: None,
                created_at: "2025-01-01T00:00:00Z".to_owned(),
                tags: vec!["fs".to_owned(), "read".to_owned(), "file".to_owned()],
            },
            TemplateRecord {
                id: 0,
                task_description: "Perform an HTTP GET request".to_owned(),
                effect_row: "NetIO, Alloc".to_owned(),
                source: concat!(
                    "#[ring(outer)] module tool;\n",
                    "pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { NetIO, Alloc } {\n",
                    "    return 0;\n",
                    "}\n",
                )
                .to_owned(),
                signature: "fn tool_main(i32, i32) -> i64".to_owned(),
                ast_node_count: 4,
                fuel_consumed: None,
                created_at: "2025-01-01T00:00:00Z".to_owned(),
                tags: vec!["http".to_owned(), "get".to_owned(), "fetch".to_owned()],
            },
        ];

        for record in &defaults {
            self.add(record)?;
        }

        Ok(())
    }
}

/// Map a rusqlite row into a [`TemplateRecord`].
fn row_to_record(row: &rusqlite::Row<'_>) -> rusqlite::Result<TemplateRecord> {
    let tags_json: String = row.get(8)?;
    // FAIL-OPEN, deliberately narrow: `add` is the only writer and always
    // serializes a valid JSON array, so a malformed `tags` cell means the
    // file was edited outside this API. Defaulting to no tags keeps the
    // record retrievable instead of letting one corrupt cell poison every
    // `list`/`search` that walks past it. Tags are search metadata only;
    // revisit this decision before they ever inform a security decision.
    let tags: Vec<String> = serde_json::from_str(&tags_json).unwrap_or_default();

    Ok(TemplateRecord {
        id: row.get::<_, i64>(0)? as u64,
        task_description: row.get(1)?,
        effect_row: row.get(2)?,
        source: row.get(3)?,
        signature: row.get(4)?,
        ast_node_count: row.get::<_, u32>(5)?,
        fuel_consumed: row.get::<_, Option<i64>>(6)?.map(|v| v as u64),
        created_at: row.get(7)?,
        tags,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_record(task: &str, tags: Vec<&str>) -> TemplateRecord {
        TemplateRecord {
            id: 0,
            task_description: task.to_owned(),
            effect_row: String::new(),
            source: "module tool;".to_owned(),
            signature: "fn tool_main(i32, i32) -> i64".to_owned(),
            ast_node_count: 1,
            fuel_consumed: None,
            created_at: "2025-06-01T00:00:00Z".to_owned(),
            tags: tags.into_iter().map(|s| s.to_owned()).collect(),
        }
    }

    fn fresh_store() -> TemplateStore {
        TemplateStore::open_in_memory().expect("an in-memory store must open")
    }

    #[test]
    fn add_assigns_a_positive_id_and_get_round_trips_the_record() {
        let store = fresh_store();
        let rec = sample_record("Echo test", vec!["echo", "test"]);
        let id = store
            .add(&rec)
            .expect("insert into a fresh store must succeed");
        assert!(id > 0, "rowids must start at 1, never 0");

        let fetched = store
            .get(id)
            .expect("get by a just-assigned id must not error")
            .expect("a just-inserted record must exist");
        assert_eq!(fetched.id, id);
        assert_eq!(fetched.task_description, "Echo test");
        assert_eq!(fetched.tags, vec!["echo", "test"]);
        assert_eq!(fetched.signature, "fn tool_main(i32, i32) -> i64");
    }

    #[test]
    fn search_matches_substrings_in_description_and_tags() {
        let store = fresh_store();
        for rec in [
            sample_record("Read a file", vec!["fs", "read"]),
            sample_record("Write a file", vec!["fs", "write"]),
            sample_record("HTTP GET", vec!["http", "get"]),
        ] {
            store
                .add(&rec)
                .expect("seeding the search corpus must succeed");
        }

        let results = store.search("file", 10).expect("search must not error");
        assert_eq!(results.len(), 2, "both `file` descriptions must match");

        let results = store.search("http", 10).expect("search must not error");
        assert_eq!(
            results.len(),
            1,
            "`http` must match via tag and description without double-counting"
        );
        assert_eq!(results[0].task_description, "HTTP GET");
    }

    #[test]
    fn list_returns_records_in_insertion_order() {
        let store = fresh_store();
        store
            .add(&sample_record("A", vec!["a"]))
            .expect("first insert must succeed");
        store
            .add(&sample_record("B", vec!["b"]))
            .expect("second insert must succeed");

        let all = store.list(100).expect("list must not error");
        assert_eq!(all.len(), 2);
        assert_eq!(all[0].task_description, "A");
        assert_eq!(all[1].task_description, "B");
    }

    #[test]
    fn seed_defaults_seeds_once_and_reseeding_is_a_no_op() {
        let store = fresh_store();
        store
            .seed_defaults()
            .expect("seeding an empty store must succeed");
        assert_eq!(store.count().expect("count must not error"), 3);

        store.seed_defaults().expect("reseeding must be accepted");
        assert_eq!(
            store.count().expect("count must not error"),
            3,
            "reseeding a non-empty store must not add rows"
        );
    }

    #[test]
    fn update_fuel_records_a_fuel_measurement() {
        let store = fresh_store();
        let id = store
            .add(&sample_record("fuel test", vec!["test"]))
            .expect("insert must succeed");

        let before = store
            .get(id)
            .expect("get must not error")
            .expect("the record must exist before the update");
        assert!(before.fuel_consumed.is_none(), "fuel must start unmeasured");

        store
            .update_fuel(id, 42_000)
            .expect("update_fuel must succeed");
        let after = store
            .get(id)
            .expect("get must not error")
            .expect("the record must survive the update");
        assert_eq!(after.fuel_consumed, Some(42_000));
    }
}
