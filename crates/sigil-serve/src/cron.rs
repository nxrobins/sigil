//! Five-field cron expressions (UTC), std-only.
//!
//! `minute hour day-of-month month day-of-week` with `*`, `*/step`,
//! `a`, `a-b`, `a-b/step`, and comma lists. Ranges: minutes 0–59,
//! hours 0–23, day-of-month 1–31, month 1–12, day-of-week 0–6 with
//! 0 = Sunday (numeric only — no names in v1).
//!
//! Day matching keeps the classic vixie-cron quirk, documented rather
//! than "fixed": when BOTH day-of-month and day-of-week are
//! restricted, a day matches if EITHER does; when only one is
//! restricted, that one decides.
//!
//! `next_fire_after` is a pure function of (spec, timestamp) so the
//! scheduler's timing logic is testable against golden values without
//! touching a wall clock. Fires are whole-minute aligned. A spec that
//! can never fire (e.g. Feb 30) returns `None` past a ~4-year search
//! horizon instead of looping forever.

use anyhow::{Context, bail};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CronSpec {
    minutes: u64,
    hours: u32,
    days_of_month: u32,
    months: u16,
    days_of_week: u8,
    dom_restricted: bool,
    dow_restricted: bool,
}

pub fn parse(expr: &str) -> anyhow::Result<CronSpec> {
    let fields: Vec<&str> = expr.split_whitespace().collect();
    if fields.len() != 5 {
        bail!(
            "cron `{expr}`: expected 5 fields (minute hour day-of-month month day-of-week), got {}",
            fields.len()
        );
    }
    let minutes = parse_field(fields[0], 0, 59).with_context(|| format!("cron `{expr}` minute"))?;
    let hours = parse_field(fields[1], 0, 23).with_context(|| format!("cron `{expr}` hour"))?;
    let dom =
        parse_field(fields[2], 1, 31).with_context(|| format!("cron `{expr}` day-of-month"))?;
    let months = parse_field(fields[3], 1, 12).with_context(|| format!("cron `{expr}` month"))?;
    let dow = parse_field(fields[4], 0, 6).with_context(|| format!("cron `{expr}` day-of-week"))?;
    Ok(CronSpec {
        minutes,
        hours: hours as u32,
        days_of_month: dom as u32,
        months: months as u16,
        days_of_week: dow as u8,
        dom_restricted: fields[2] != "*",
        dow_restricted: fields[4] != "*",
    })
}

/// One field → a bitmask over [min, max]. Comma list of atoms; each
/// atom is `*`, `a`, or `a-b`, optionally `/step`.
fn parse_field(field: &str, min: u32, max: u32) -> anyhow::Result<u64> {
    if field.is_empty() {
        bail!("empty field");
    }
    let mut mask: u64 = 0;
    for atom in field.split(',') {
        let (range, step) = match atom.split_once('/') {
            Some((range, step)) => {
                let step: u32 = step
                    .parse()
                    .with_context(|| format!("bad step in `{atom}`"))?;
                if step == 0 {
                    bail!("step 0 in `{atom}`");
                }
                (range, step)
            }
            None => (atom, 1),
        };
        let (lo, hi) = if range == "*" {
            (min, max)
        } else if let Some((a, b)) = range.split_once('-') {
            let lo: u32 = a
                .parse()
                .with_context(|| format!("bad range in `{atom}`"))?;
            let hi: u32 = b
                .parse()
                .with_context(|| format!("bad range in `{atom}`"))?;
            (lo, hi)
        } else {
            let v: u32 = range
                .parse()
                .with_context(|| format!("bad value `{atom}`"))?;
            (v, v)
        };
        if lo < min || hi > max || lo > hi {
            bail!("`{atom}` outside {min}..={max}");
        }
        let mut v = lo;
        while v <= hi {
            mask |= 1 << v;
            v += step;
        }
    }
    Ok(mask)
}

impl CronSpec {
    fn minute_matches(&self, minute: u32) -> bool {
        self.minutes & (1 << minute) != 0
    }
    fn hour_matches(&self, hour: u32) -> bool {
        self.hours & (1 << hour) != 0
    }
    fn month_matches(&self, month: u32) -> bool {
        self.months & (1 << month) != 0
    }
    /// The vixie OR rule (see module docs).
    fn day_matches(&self, dom: u32, dow: u32) -> bool {
        let dom_hit = self.days_of_month & (1 << dom) != 0;
        let dow_hit = self.days_of_week & (1 << dow) != 0;
        match (self.dom_restricted, self.dow_restricted) {
            (true, true) => dom_hit || dow_hit,
            (true, false) => dom_hit,
            (false, true) => dow_hit,
            (false, false) => true,
        }
    }
}

/// Days since 1970-01-01 → (year, month, day). Hinnant's civil_from_days.
fn civil_from_days(z: i64) -> (i64, u32, u32) {
    let z = z + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let m = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// (year, month, day) → days since 1970-01-01. Hinnant's days_from_civil.
fn days_from_civil(y: i64, m: u32, d: u32) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = if y >= 0 { y } else { y - 399 } / 400;
    let yoe = y - era * 400;
    let mp = if m > 2 { m - 3 } else { m + 9 } as i64;
    let doy = (153 * mp + 2) / 5 + i64::from(d) - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146_097 + doe - 719_468
}

const MINUTES_PER_DAY: u64 = 24 * 60;

/// Smallest whole-minute UTC timestamp STRICTLY after `after_ms` that
/// matches `spec`; `None` if nothing matches within ~4 years.
pub fn next_fire_after(spec: &CronSpec, after_ms: u64) -> Option<u64> {
    let mut minute = after_ms / 60_000 + 1;
    let horizon = minute + 4 * 366 * MINUTES_PER_DAY;
    while minute < horizon {
        let day = (minute / MINUTES_PER_DAY) as i64;
        let (year, month, dom) = civil_from_days(day);
        if !spec.month_matches(month) {
            let (next_year, next_month) = if month == 12 {
                (year + 1, 1)
            } else {
                (year, month + 1)
            };
            minute = days_from_civil(next_year, next_month, 1) as u64 * MINUTES_PER_DAY;
            continue;
        }
        let dow = ((day + 4).rem_euclid(7)) as u32;
        if !spec.day_matches(dom, dow) {
            minute = (day as u64 + 1) * MINUTES_PER_DAY;
            continue;
        }
        let minute_of_day = minute % MINUTES_PER_DAY;
        let hour = (minute_of_day / 60) as u32;
        if !spec.hour_matches(hour) {
            minute = day as u64 * MINUTES_PER_DAY + (u64::from(hour) + 1) * 60;
            continue;
        }
        if !spec.minute_matches((minute_of_day % 60) as u32) {
            minute += 1;
            continue;
        }
        return Some(minute * 60_000);
    }
    None
}

#[cfg(test)]
mod mask_sanity {
    use super::*;

    // The full-range masks `parse_field` must produce for `*`.
    const MINUTES_ALL: u64 = (1 << 60) - 1;
    const HOURS_ALL: u32 = (1 << 24) - 1;
    const DOM_ALL: u32 = ((1u32 << 31) - 1) << 1;
    const MONTHS_ALL: u16 = ((1u16 << 12) - 1) << 1;
    const DOW_ALL: u8 = (1 << 7) - 1;

    #[test]
    fn star_masks_match_the_documented_constants() {
        let spec = parse("* * * * *").expect("full wildcard parses");
        assert_eq!(spec.minutes, MINUTES_ALL);
        assert_eq!(spec.hours, HOURS_ALL);
        assert_eq!(spec.days_of_month, DOM_ALL);
        assert_eq!(spec.months, MONTHS_ALL);
        assert_eq!(spec.days_of_week, DOW_ALL);
    }
}
