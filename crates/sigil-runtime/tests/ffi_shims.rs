//! Phase 5a-2: tests for the new FFI shims (fs_write, crypto_sha256/512,
//! time_now, random_bytes) plus the grant-cap (R808) check.
//!
//! Each shim is exercised end-to-end through `execute_ephemeral` with a
//! Sigil tool that calls into it. Grant-rejection paths verify 403 is
//! returned without the appropriate grant.

use std::path::PathBuf;

use sigil_compiler::compile_tool;
use sigil_runtime::{
    FsGrant, FsWriteGrant, IoGrants, MAX_GRANTS_PER_CATEGORY, NetGrant, RandomGrant, TimeGrant,
    execute_ephemeral,
};

const FUEL_BUDGET: u64 = 1_000_000;

fn forge_raw(source: &str, input: &[u8], grants: &IoGrants) -> sigil_runtime::ToolResult {
    let compiled = compile_tool(source).expect("compile");
    execute_ephemeral(&compiled.wasm, input, FUEL_BUDGET, grants).expect("execute")
}

// ── Grant cap (R808 / I26) ────────────────────────────────────────────────

#[test]
fn r808_grant_cap_per_category() {
    // 257 fs grants exceeds MAX_GRANTS_PER_CATEGORY (256).
    let grants = IoGrants {
        fs: (0..=MAX_GRANTS_PER_CATEGORY)
            .map(|i| FsGrant {
                root: PathBuf::from(format!("/tmp/grant_{i}")),
            })
            .collect(),
        ..Default::default()
    };
    let err = grants.validate().expect_err("should fail validation");
    assert_eq!(err.category, "fs");
    assert_eq!(err.len, MAX_GRANTS_PER_CATEGORY + 1);
    assert_eq!(err.max, MAX_GRANTS_PER_CATEGORY);
}

#[test]
fn r808_at_cap_is_allowed() {
    // Exactly MAX entries is OK.
    let grants = IoGrants {
        net: (0..MAX_GRANTS_PER_CATEGORY)
            .map(|i| NetGrant {
                host_pattern: format!("host{i}.example.com"),
                methods: vec![],
            })
            .collect(),
        ..Default::default()
    };
    grants.validate().expect("at-cap should pass");
}

#[test]
fn r808_each_category_independently_capped() {
    for category in ["fs", "fs_write", "net", "time", "random"] {
        let grants = match category {
            "fs" => IoGrants {
                fs: (0..=MAX_GRANTS_PER_CATEGORY)
                    .map(|i| FsGrant {
                        root: PathBuf::from(format!("/p{i}")),
                    })
                    .collect(),
                ..Default::default()
            },
            "fs_write" => IoGrants {
                fs_write: (0..=MAX_GRANTS_PER_CATEGORY)
                    .map(|i| FsWriteGrant {
                        root: PathBuf::from(format!("/p{i}")),
                    })
                    .collect(),
                ..Default::default()
            },
            "net" => IoGrants {
                net: (0..=MAX_GRANTS_PER_CATEGORY)
                    .map(|i| NetGrant {
                        host_pattern: format!("h{i}"),
                        methods: vec![],
                    })
                    .collect(),
                ..Default::default()
            },
            "time" => IoGrants {
                time: vec![TimeGrant::Wall; MAX_GRANTS_PER_CATEGORY + 1],
                ..Default::default()
            },
            "random" => IoGrants {
                random: vec![RandomGrant::Secure; MAX_GRANTS_PER_CATEGORY + 1],
                ..Default::default()
            },
            _ => unreachable!(),
        };
        let err = grants
            .validate()
            .unwrap_err_or_else(|| panic!("expected validation failure for {category}"));
        assert_eq!(err.category, category, "wrong category in error");
    }
}

// ── crypto_sha256 (pure compute, no grant required) ──────────────────────

#[test]
fn crypto_sha256_known_vector() {
    // SHA-256 of empty string = e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855
    let source = r#"
#[ring(outer)] #[trusted]
module tool;

extern "C" fn crypto_sha256(input: i32, input_len: i32) -> i64 ! { FFI, Unsafe };

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {
    return crypto_sha256(input_ptr, input_len);
}
"#;
    let result = forge_raw(source, b"", &IoGrants::none());
    // Output should be 32 bytes — the SHA-256 digest.
    assert_eq!(result.output.len(), 32, "SHA-256 output must be 32 bytes");
    // First 4 bytes of empty-string SHA-256: e3 b0 c4 42
    assert_eq!(&result.output[..4], &[0xe3, 0xb0, 0xc4, 0x42]);
}

#[test]
fn crypto_sha256_deterministic_across_runs() {
    let source = r#"
#[ring(outer)] #[trusted]
module tool;
extern "C" fn crypto_sha256(input: i32, input_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {
    return crypto_sha256(input_ptr, input_len);
}
"#;
    let r1 = forge_raw(source, b"determinism check", &IoGrants::none());
    let r2 = forge_raw(source, b"determinism check", &IoGrants::none());
    assert_eq!(
        r1.output, r2.output,
        "I3: pure compute must be deterministic"
    );
}

// ── crypto_sha512 ──────────────────────────────────────────────────────────

#[test]
fn crypto_sha512_known_vector_length() {
    let source = r#"
#[ring(outer)] #[trusted]
module tool;
extern "C" fn crypto_sha512(input: i32, input_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {
    return crypto_sha512(input_ptr, input_len);
}
"#;
    let result = forge_raw(source, b"", &IoGrants::none());
    assert_eq!(result.output.len(), 64, "SHA-512 output must be 64 bytes");
}

// ── time_now (grant-gated) ────────────────────────────────────────────────
//
// Wasm-level integration tests for `time_now` are deferred to 5a-3
// because the shim returns a raw i64 (Unix-epoch ms) that doesn't fit
// the packed-pointer ABI of `tool_main`. The stdlib `time` module (5a-3)
// will provide a wrapper that renders the timestamp as a decimal string
// and returns a packed pointer. For now, the grant-check unit test
// below validates the host-side behavior.

#[test]
fn time_now_grant_check() {
    let no_grants = IoGrants::none();
    assert!(!no_grants.time_allowed(TimeGrant::Wall));

    let with_grant = IoGrants {
        time: vec![TimeGrant::Wall],
        ..Default::default()
    };
    assert!(with_grant.time_allowed(TimeGrant::Wall));
}

// ── random_bytes (grant-gated, capped at 64 KB) ──────────────────────────

#[test]
fn random_bytes_grant_check() {
    // Without a Random grant, random_bytes returns 403.
    // We test the grant logic directly here; the wasm-level test
    // would require a tool_main that consumes random_bytes' output.
    let no_grants = IoGrants::none();
    assert!(!no_grants.random_allowed(RandomGrant::Secure));

    let with_grant = IoGrants {
        random: vec![RandomGrant::Secure],
        ..Default::default()
    };
    assert!(with_grant.random_allowed(RandomGrant::Secure));
}

// ── fs_list (directory listing, grant-gated, deterministic) ───────────────

const FS_LIST_TOOL: &str = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn fs_list(path: i32, path_len: i32) -> i64 ! { FFI, Unsafe };
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { FsIO, Alloc, FFI, Unsafe } {
    return fs_list(input_ptr, input_len);
}
"#;

fn unique_dir(tag: &str) -> PathBuf {
    // Mirrors kv_shims.rs's temp-dir approach (no tempfile dev-dep).
    let dir = std::env::temp_dir().join(format!("sigil_fs_list_{tag}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    dir
}

#[test]
fn fs_list_returns_sorted_newline_joined_entries() {
    let dir = unique_dir("entries");
    // create out of order to prove the shim sorts, not the filesystem
    std::fs::write(dir.join("b.txt"), b"").unwrap();
    std::fs::write(dir.join("a.txt"), b"").unwrap();
    std::fs::create_dir(dir.join("sub")).unwrap();
    let canonical = std::fs::canonicalize(&dir).unwrap();

    let grants = IoGrants {
        fs: vec![FsGrant {
            root: canonical.clone(),
        }],
        ..Default::default()
    };
    let result = forge_raw(
        FS_LIST_TOOL,
        canonical.to_str().unwrap().as_bytes(),
        &grants,
    );
    assert_eq!(result.output, b"a.txt\nb.txt\nsub");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fs_list_empty_dir_is_empty_output() {
    let dir = unique_dir("empty");
    let canonical = std::fs::canonicalize(&dir).unwrap();
    let grants = IoGrants {
        fs: vec![FsGrant {
            root: canonical.clone(),
        }],
        ..Default::default()
    };
    let result = forge_raw(
        FS_LIST_TOOL,
        canonical.to_str().unwrap().as_bytes(),
        &grants,
    );
    assert_eq!(result.output, b"");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fs_list_denied_outside_grant_is_403() {
    let dir = unique_dir("denied");
    let canonical = std::fs::canonicalize(&dir).unwrap();
    // grant a DIFFERENT root; listing `dir` must be refused
    let grants = IoGrants {
        fs: vec![FsGrant {
            root: PathBuf::from("/nonexistent-grant-root"),
        }],
        ..Default::default()
    };
    let compiled = compile_tool(FS_LIST_TOOL).expect("compile");
    let err = execute_ephemeral(
        &compiled.wasm,
        canonical.to_str().unwrap().as_bytes(),
        FUEL_BUDGET,
        &grants,
    )
    .expect_err("listing outside the grant should be denied");
    match err {
        sigil_runtime::ToolError::Trapped { message } => assert!(
            message.contains("tool returned error (403)"),
            "got: {message}"
        ),
        other => panic!("expected -403 trap, got {other:?}"),
    }
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn fs_list_on_a_file_is_404() {
    let dir = unique_dir("onfile");
    let file = dir.join("f.txt");
    std::fs::write(&file, b"hi").unwrap();
    let canonical = std::fs::canonicalize(&file).unwrap();
    let grants = IoGrants {
        fs: vec![FsGrant {
            root: std::fs::canonicalize(&dir).unwrap(),
        }],
        ..Default::default()
    };
    let compiled = compile_tool(FS_LIST_TOOL).expect("compile");
    let err = execute_ephemeral(
        &compiled.wasm,
        canonical.to_str().unwrap().as_bytes(),
        FUEL_BUDGET,
        &grants,
    )
    .expect_err("listing a regular file should be -404");
    match err {
        sigil_runtime::ToolError::Trapped { message } => assert!(
            message.contains("tool returned error (404)"),
            "got: {message}"
        ),
        other => panic!("expected -404 trap, got {other:?}"),
    }
    let _ = std::fs::remove_dir_all(&dir);
}

// ── fs_write (grant-gated) ────────────────────────────────────────────────

#[test]
fn fs_write_grant_check() {
    let no_grants = IoGrants::none();
    let path = std::path::Path::new("/some/path");
    assert!(!no_grants.fs_write_allowed(path));

    let grants = IoGrants {
        fs_write: vec![FsWriteGrant {
            root: PathBuf::from("/some"),
        }],
        ..Default::default()
    };
    assert!(grants.fs_write_allowed(path));
}

#[test]
fn fs_write_separate_from_fs_read() {
    // A read grant does NOT confer write access.
    let read_only = IoGrants {
        fs: vec![FsGrant {
            root: PathBuf::from("/data"),
        }],
        ..Default::default()
    };
    let path = std::path::Path::new("/data/file.txt");
    assert!(read_only.fs_read_allowed(path));
    assert!(
        !read_only.fs_write_allowed(path),
        "read grant must not confer write access"
    );
}

// Tiny helper because Result<T, E> doesn't have unwrap_err_or_else.
trait UnwrapErrOrElse<T, E> {
    fn unwrap_err_or_else(self, f: impl FnOnce() -> E) -> E;
}

impl<T: std::fmt::Debug, E> UnwrapErrOrElse<T, E> for Result<T, E> {
    fn unwrap_err_or_else(self, f: impl FnOnce() -> E) -> E {
        match self {
            Err(e) => e,
            Ok(v) => {
                let _ = v;
                f()
            }
        }
    }
}

// ── Frozen-time grant (deterministic) ─────────────────────────────────────

const TIME_TOOL_SRC: &str = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn time_now() -> i64 ! { FFI, Unsafe };

pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc, FFI, Unsafe } {
    let ms: i64 @Internal = time_now();
    let buf: i64 @Internal = alloc(8);
    store8(buf + 0, ms & 255);
    store8(buf + 1, (ms >> 8) & 255);
    store8(buf + 2, (ms >> 16) & 255);
    store8(buf + 3, (ms >> 24) & 255);
    store8(buf + 4, (ms >> 32) & 255);
    store8(buf + 5, (ms >> 40) & 255);
    store8(buf + 6, (ms >> 48) & 255);
    store8(buf + 7, (ms >> 56) & 255);
    return (buf * 4294967296) + 8;
}
"#;

#[test]
fn time_now_frozen_returned_verbatim() {
    // An arbitrary deterministic ms value. The point of the test is
    // round-trip equality, not the calendar interpretation.
    let frozen_ms: i64 = 1_779_177_600_000; // = 2026-05-19T08:00:00Z
    let grants = IoGrants {
        time: vec![TimeGrant::Frozen(frozen_ms)],
        ..Default::default()
    };
    let result = forge_raw(TIME_TOOL_SRC, b"", &grants);
    assert_eq!(result.output.len(), 8);
    let ms = i64::from_le_bytes(result.output[..8].try_into().unwrap());
    assert_eq!(
        ms, frozen_ms,
        "time_now must return the Frozen value verbatim, not wall clock"
    );
}

#[test]
fn frozen_time_helper_returns_first_frozen() {
    let g = IoGrants {
        time: vec![TimeGrant::Frozen(42), TimeGrant::Wall],
        ..Default::default()
    };
    assert_eq!(g.frozen_time(), Some(42));
    // Wall alone has no frozen value:
    let g2 = IoGrants {
        time: vec![TimeGrant::Wall],
        ..Default::default()
    };
    assert_eq!(g2.frozen_time(), None);
}

#[test]
fn frozen_grant_does_not_imply_wall_grant() {
    // Backward compat invariant: time_allowed(Wall) checks for Wall
    // specifically. Frozen alone does NOT make time_allowed(Wall) true.
    let g = IoGrants {
        time: vec![TimeGrant::Frozen(0)],
        ..Default::default()
    };
    assert!(!g.time_allowed(TimeGrant::Wall));
    assert_eq!(g.frozen_time(), Some(0));
}

// ── Seeded-random grant (deterministic, xorshift64*) ──────────────────────

const RANDOM_TOOL_SRC: &str = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn random_bytes(out_len: i32) -> i64 ! { FFI, Unsafe };

// input_len is i32; caller passes a 16-byte input buffer so input_len=16.
pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {
    return random_bytes(input_len);
}
"#;

#[test]
fn random_bytes_seeded_matches_golden_vector_seed1() {
    // Golden vector documented on RandomGrant::Seeded.
    // For seed=1, first 16 LE-packed bytes:
    let expected: [u8; 16] = [
        0x5d, 0xc4, 0x01, 0x4f, 0x62, 0xcf, 0xfa, 0xba, 0x5d, 0x68, 0x07, 0xe5, 0x91, 0x68, 0xda,
        0x02,
    ];
    let grants = IoGrants {
        random: vec![RandomGrant::Seeded(1)],
        ..Default::default()
    };
    // 16-byte input so tool_main's i32 input_len evaluates to 16 inside the tool.
    let input = [0u8; 16];
    let result = forge_raw(RANDOM_TOOL_SRC, &input, &grants);
    assert_eq!(result.output.len(), 16);
    assert_eq!(
        &result.output[..],
        &expected[..],
        "xorshift64* with seed=1 must match the pinned golden vector"
    );
}

#[test]
fn random_bytes_seeded_resets_per_execution() {
    // Two consecutive execute_ephemeral calls with the same seeded
    // grant must produce identical first-byte output. The PRNG state
    // lives on EphemeralData (per-Store); it must NOT survive past
    // the execution.
    let grants = IoGrants {
        random: vec![RandomGrant::Seeded(1)],
        ..Default::default()
    };
    let input = [0u8; 16];
    let r1 = forge_raw(RANDOM_TOOL_SRC, &input, &grants);
    let r2 = forge_raw(RANDOM_TOOL_SRC, &input, &grants);
    assert_eq!(
        r1.output, r2.output,
        "seeded PRNG state must reset between executions"
    );
}

#[test]
fn seeded_grant_does_not_imply_secure_grant() {
    // Backward compat invariant.
    let g = IoGrants {
        random: vec![RandomGrant::Seeded(7)],
        ..Default::default()
    };
    assert!(!g.random_allowed(RandomGrant::Secure));
    assert_eq!(g.seeded_random(), Some(7));
}

#[test]
fn validate_rejects_seeded_zero() {
    // Seeded(0) is a quiet way to break determinism — xorshift on 0
    // produces 0 forever. Grant validation rejects it.
    let g = IoGrants {
        random: vec![RandomGrant::Seeded(0)],
        ..Default::default()
    };
    let err = g.validate().expect_err("Seeded(0) must be rejected");
    assert_eq!(err.category, "random_seeded_zero");

    // Nonzero seed validates.
    let g2 = IoGrants {
        random: vec![RandomGrant::Seeded(1)],
        ..Default::default()
    };
    assert!(g2.validate().is_ok());
}

#[test]
fn execute_ephemeral_rejects_seeded_zero() {
    // End-to-end: execute_ephemeral itself returns an error when
    // grants fail validation. Belt-and-braces with the unit test above.
    let grants = IoGrants {
        random: vec![RandomGrant::Seeded(0)],
        ..Default::default()
    };
    let compiled = compile_tool(RANDOM_TOOL_SRC).expect("compile");
    let input = [0u8; 16];
    let result = execute_ephemeral(&compiled.wasm, &input, FUEL_BUDGET, &grants);
    assert!(result.is_err(), "Seeded(0) must reject at execute time");
}

// Tool that calls random_bytes(input_len). Caller controls the
// requested-byte count by sizing the input buffer.
const RANDOM_BYTES_FROM_INPUT_LEN_TOOL: &str = r#"
#[ring(outer)] #[trusted] module tool;
extern "C" fn random_bytes(out_len: i32) -> i64 ! { FFI, Unsafe };

pub fn tool_main(input_ptr: i32, input_len: i32) -> i64 ! { Alloc, FFI, Unsafe } {
    return random_bytes(input_len);
}
"#;

#[test]
fn random_bytes_zero_rejected() {
    // Reject random_bytes(0): the 0-byte buffer's contents are
    // unspecified, and a SIGIL caller using load8(ptr) would read
    // stale memory. Fail at the FFI shim with error code 400, which
    // the runtime surfaces as a Trapped result containing "(400)".
    let grants = IoGrants {
        random: vec![RandomGrant::Seeded(1)],
        ..Default::default()
    };
    let compiled = compile_tool(RANDOM_BYTES_FROM_INPUT_LEN_TOOL).expect("compile");
    // Empty input → input_len = 0 → random_bytes(0) → expect 400 trap.
    let err = execute_ephemeral(&compiled.wasm, b"", FUEL_BUDGET, &grants)
        .expect_err("random_bytes(0) must fail");
    match err {
        sigil_runtime::ToolError::Trapped { message } => {
            assert!(
                message.contains("400"),
                "expected error 400 in trap message, got `{message}`"
            );
        }
        other => panic!("expected Trapped, got {other:?}"),
    }
}

#[test]
fn seeded_random_concurrent_isolation() {
    // Spawn 4 threads, each running execute_ephemeral with the same
    // Seeded grant. Each thread gets its own Store (and therefore its
    // own random_state Option<u64>); all four must produce the same
    // 16-byte output. If state leaked across executions through any
    // process-wide static, threads would interfere and outputs
    // would differ.
    use std::sync::Arc;
    use std::thread;

    let grants = Arc::new(IoGrants {
        random: vec![RandomGrant::Seeded(1)],
        ..Default::default()
    });
    let compiled = Arc::new(compile_tool(RANDOM_TOOL_SRC).expect("compile"));

    let handles: Vec<_> = (0..4)
        .map(|_| {
            let g = Arc::clone(&grants);
            let c = Arc::clone(&compiled);
            thread::spawn(move || {
                let input = [0u8; 16];
                execute_ephemeral(&c.wasm, &input, FUEL_BUDGET, &g).expect("execute")
            })
        })
        .collect();

    let outputs: Vec<Vec<u8>> = handles
        .into_iter()
        .map(|h| h.join().expect("thread panicked").output)
        .collect();

    let first = &outputs[0];
    for (i, out) in outputs.iter().enumerate() {
        assert_eq!(
            out, first,
            "thread {i} output differs from thread 0 — \
             cross-execution state leak in the seeded PRNG"
        );
    }
}
