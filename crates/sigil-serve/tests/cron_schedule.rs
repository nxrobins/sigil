//! Cron parsing + next-fire golden tests. Timestamps generated with an
//! independent oracle (Python `datetime`, UTC) and hardcoded — the
//! civil-date math must agree with the outside world, not with itself.

use sigil_serve::cron::{next_fire_after, parse};

/// 2026-07-28 12:34:56 UTC — a Tuesday.
const AFTER: u64 = 1_785_242_096_000;

#[test]
fn next_fire_golden_values() {
    let cases: &[(&str, u64)] = &[
        // Top of the next hour.
        ("0 * * * *", 1_785_243_600_000), // 2026-07-28 13:00
        // Daily at 02:30 — already past today, so tomorrow.
        ("30 2 * * *", 1_785_292_200_000), // 2026-07-29 02:30
        // First of the month.
        ("0 0 1 * *", 1_785_542_400_000), // 2026-08-01 00:00
        // Next Sunday midnight (0 = Sunday).
        ("0 0 * * 0", 1_785_628_800_000), // 2026-08-02 00:00
        // Quarter-hour steps.
        ("*/15 * * * *", 1_785_242_700_000), // 2026-07-28 12:45
        // Comma list picks the nearest member.
        ("50,40 12 * * *", 1_785_242_400_000), // 2026-07-28 12:40
    ];
    for (expr, want) in cases {
        let spec = parse(expr).unwrap_or_else(|e| panic!("{expr}: {e:#}"));
        assert_eq!(
            next_fire_after(&spec, AFTER),
            Some(*want),
            "next fire for `{expr}` after 2026-07-28T12:34:56Z"
        );
    }
}

#[test]
fn vixie_or_rule_day_of_month_or_day_of_week() {
    // "0 0 13 * 5": with BOTH day fields restricted, EITHER matches —
    // the next hit after the reference Tuesday is Friday 2026-07-31,
    // which is not the 13th.
    let spec = parse("0 0 13 * 5").unwrap();
    assert_eq!(next_fire_after(&spec, AFTER), Some(1_785_456_000_000));
}

#[test]
fn strictly_after_and_minute_alignment() {
    let spec = parse("0 12 * * *").unwrap();
    // One second before noon: fires AT noon (next whole minute > t).
    assert_eq!(
        next_fire_after(&spec, 1_785_239_999_000),
        Some(1_785_240_000_000)
    );
    // Exactly noon: strictly after — fires tomorrow.
    let noon = 1_785_240_000_000;
    assert_eq!(
        next_fire_after(&spec, noon),
        Some(noon + 24 * 60 * 60 * 1000)
    );
}

#[test]
fn unsatisfiable_spec_returns_none() {
    // February 30th never exists.
    let spec = parse("0 0 30 2 *").unwrap();
    assert_eq!(next_fire_after(&spec, AFTER), None);
}

#[test]
fn parse_rejections() {
    let bad = [
        "60 * * * *",  // minute out of range
        "* * * * * *", // six fields
        "* * * *",     // four fields
        "a * * * *",   // not a number
        "*/0 * * * *", // zero step
        "* * 0 * *",   // day-of-month 0
        "* * * 13 *",  // month 13
        "* * * * 7",   // day-of-week 7 (0-6 only)
        "5-2 * * * *", // inverted range
        ", * * * *",   // empty list atom
    ];
    for expr in bad {
        assert!(parse(expr).is_err(), "`{expr}` must be rejected");
    }
}

#[test]
fn parse_accepts_the_documented_grammar() {
    for expr in [
        "* * * * *",
        "0 0 * * *",
        "*/5 8-18 * * 1-5",
        "0,30 */2 1,15 1-6/2 0,6",
    ] {
        parse(expr).unwrap_or_else(|e| panic!("`{expr}` should parse: {e:#}"));
    }
}
