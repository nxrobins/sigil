//! The `secret` grant in a service config — host-held credentials for
//! `http::post_secret`.
//!
//! `post_secret` exists so an API key never enters guest memory: the guest
//! writes `{{secret:NAME}}` and the host substitutes the value on the way out.
//! That is only reachable from a served tool if the config can name the secret,
//! so these tests cover the parse and the fail-closed edges.

mod common;

use common::{TempDir, write_service};
use sigil_serve::config::Config;

const ECHO: &str = "module tool;\n\
pub fn tool_main(input_ptr: i64, input_len: i64) -> i64 ! { Alloc } {\n\
    return input_ptr << 32 | input_len;\n\
}\n";

fn config_with_grants(label: &str, grants: &str) -> Result<(Config, std::path::PathBuf), String> {
    let dir = TempDir::new(label);
    let config = format!(
        r#"{{
  "tools": {{ "t": {{ "source": "t.sigil", "grants": {grants} }} }},
  "http": {{ "bind": "127.0.0.1:0", "routes": [ {{ "path": "/t", "tool": "t" }} ] }}
}}"#
    );
    let path = write_service(dir.path(), &config, &[("t.sigil", ECHO)]);
    // Keep the TempDir alive for the caller by leaking it: these are
    // short-lived test processes and the config borrows the on-disk files.
    std::mem::forget(dir);
    Config::load(&path).map_err(|e| format!("{e:#}"))
}

#[test]
fn secret_grant_parses_and_reaches_the_runtime() {
    let (config, _base) = config_with_grants(
        "secret_ok",
        r#"{ "secret": ["anthropic=sk-test-value", "other=second"] }"#,
    )
    .expect("a `secret` grant must be a recognized config field");
    let grants = config.tools["t"]
        .grants
        .to_io_grants("t")
        .expect("grants build");
    assert_eq!(grants.secret.len(), 2);
    assert_eq!(grants.secret[0].name, "anthropic");
    assert_eq!(grants.secret[0].value, b"sk-test-value");
    assert_eq!(grants.secret[1].name, "other");
}

#[test]
fn secret_value_may_contain_equals_signs() {
    // Split on the FIRST `=` only — base64 and JWT-shaped credentials
    // routinely contain padding `=`.
    let (config, _base) =
        config_with_grants("secret_equals", r#"{ "secret": ["tok=abc==def="] }"#).expect("parses");
    let grants = config.tools["t"]
        .grants
        .to_io_grants("t")
        .expect("grants build");
    assert_eq!(grants.secret[0].name, "tok");
    assert_eq!(grants.secret[0].value, b"abc==def=");
}

#[test]
fn secret_entry_without_a_value_separator_is_refused() {
    let (config, _base) =
        config_with_grants("secret_malformed", r#"{ "secret": ["anthropic"] }"#).expect("parses");
    let err = config.tools["t"]
        .grants
        .to_io_grants("t")
        .expect_err("a malformed secret grant must refuse to boot");
    let message = format!("{err:#}");
    assert!(message.contains("NAME=VALUE"), "got: {message}");
}

#[test]
fn secret_entry_with_an_empty_name_is_refused() {
    let (config, _base) =
        config_with_grants("secret_empty_name", r#"{ "secret": ["=value"] }"#).expect("parses");
    let err = config.tools["t"]
        .grants
        .to_io_grants("t")
        .expect_err("an unnamed secret can never match a placeholder");
    assert!(format!("{err:#}").contains("empty name"));
}

#[test]
fn a_refused_secret_grant_does_not_echo_the_secret() {
    // The error text travels to logs and to the operator's terminal. A
    // malformed entry is still a credential.
    let (config, _base) = config_with_grants(
        "secret_no_echo",
        r#"{ "secret": ["sk-live-do-not-log-this"] }"#,
    )
    .expect("parses");
    let err = config.tools["t"]
        .grants
        .to_io_grants("t")
        .expect_err("malformed entry is refused");
    let message = format!("{err:#}");
    assert!(
        !message.contains("sk-live-do-not-log-this"),
        "the diagnostic leaked the secret: {message}"
    );
}

#[test]
fn omitting_the_secret_grant_is_fail_closed() {
    let (config, _base) = config_with_grants("secret_absent", r#"{ }"#).expect("parses");
    let grants = config.tools["t"]
        .grants
        .to_io_grants("t")
        .expect("grants build");
    assert!(
        grants.secret.is_empty(),
        "no secret grant means every placeholder is denied"
    );
}

#[test]
fn an_unknown_grant_field_still_refuses_to_boot() {
    // Conservation: adding `secret` must not have loosened `deny_unknown_fields`.
    let err = config_with_grants("secret_typo", r#"{ "secrets": ["a=b"] }"#)
        .expect_err("a typo'd grant name must not silently widen the sandbox");
    assert!(
        err.contains("secrets") || err.contains("unknown field"),
        "got: {err}"
    );
}
