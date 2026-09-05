//! Source-level single-writer / forbidden-token gate for `stdlib/sigil/map.sigil`
//! (CF-D2 / CF-D4 / CF-D5), mirroring `vec_quarantine.rs`.
//!
//! The two deadliest dense-map bugs — a stray `self.vals.push` or
//! `self.keys.push` on the overwrite/grow path — are behaviorally INVISIBLE
//! leaks (`count`-based tests can't see them). Only source-level enforcement
//! that the value log and the key log each have exactly ONE writer catches
//! them. CF-D5 forbids `%` (a negative hash `% slots` gives a negative
//! remainder → out of range; the home slot must be `& (slots-1)`).

const MAP: &str = include_str!("../../../stdlib/sigil/map.sigil");

/// map.sigil with line comments stripped, so a token inside a `//` comment is
/// not counted.
fn code() -> String {
    MAP.lines()
        .map(|l| l.split("//").next().unwrap_or(l))
        .collect::<Vec<_>>()
        .join("\n")
}

fn count(needle: &str) -> usize {
    code().matches(needle).count()
}

#[test]
fn vals_push_is_single_writer() {
    // CF-D2: `vals.len() == count` ⇒ exactly ONE `self.vals.push`, in the
    // EMPTY→OCCUPIED branch of `insert`; never on overwrite, never in `grow`.
    assert_eq!(
        count("self.vals.push"),
        1,
        "`self.vals.push` must appear exactly once (the new-key branch of insert)"
    );
}

#[test]
fn keys_push_is_single_writer() {
    // CF-D4: the dense key log is append-only and only a NEW key pushes — exactly
    // one `self.keys.push` (the new-key branch of insert); overwrite pushes
    // nothing, and `grow` rebuilds only the i64 slot arrays (keys/vals are dense
    // with stable indices, never touched on grow).
    assert_eq!(
        count("self.keys.push"),
        1,
        "`self.keys.push` must appear exactly once (the new-key branch of insert)"
    );
}

#[test]
fn no_modulo_for_home_slot() {
    // CF-D5: the home slot is `hash & (slots - 1)`, never `%`/`I64RemS` (which on
    // a frequently-negative hash yields a negative remainder → out of range).
    assert_eq!(
        count(" % "),
        0,
        "map.sigil must not use `%` for slot math — use `& (slots - 1)`"
    );
}

#[test]
fn no_inline_str_hash_loop() {
    // CM-T6: there is exactly ONE canonical `str` hash (`traits::str_hash`, DJB2
    // seed 5381 shift 5). map.sigil obtains a key's hash ONLY through the `Hash`
    // trait (`key.hash()`) — it carries no private byte-hash loop and no surviving
    // `strmap_hash`. `byte_at` (the only way to read key bytes) and the old fn
    // name must both be absent; a second hash copy here would silently diverge.
    assert_eq!(
        count("strmap_hash"),
        0,
        "map.sigil must not define a private `strmap_hash` — hashing is `key.hash()` (CM-T6)"
    );
    assert_eq!(
        count("byte_at"),
        0,
        "map.sigil must not iterate key bytes — the one canonical str hash lives in traits.sigil (CM-T6)"
    );
}
