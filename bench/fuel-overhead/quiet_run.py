#!/usr/bin/env python3
"""Quiet-window runner for the fuel-instrumentation runtime overhead harness.

PERFORMANCE.md publishes the harness's numbers only from an idle machine, and
"idle" is something the runner proves rather than something the author asserts:
this script samples total CPU load once per second for a full window, refuses to
start the harness until the window's mean and peak are under the thresholds
with no compiler process alive, keeps sampling while the harness runs, and
writes every sample beside the harness's own output so the host state ships
with the run. It then pins the harness to one logical CPU at high priority,
which is how the 2026-09-20 quiet-window runner drove it (that runner lived in
a scratch directory with hard-coded paths; this one is the same procedure with
repo-relative defaults, so the redo is one command from the repository root):

    python bench/fuel-overhead/quiet_run.py

Build the harness FIRST, on its own (`cargo build --release
--no-default-features -p sigil-runtime --example fuel_overhead`); the build is
itself load, and this script refuses to build anything.

Failure direction: every gate here fails CLOSED. No harness binary, a host that
never goes idle within --max-wait, an affinity or priority call that fails on
this platform, or a non-zero harness exit each stop the run with a message, and
nothing is written that looks like a publishable result. A run with relaxed
thresholds is possible (--idle-mean, --idle-max, --idle-seconds) but the values
used are recorded in host_state.json, so a relaxed run cannot pass as a strict
one.

Outputs, in --out (default bench/fuel-overhead/<YYYY-MM-DD>-idle):

- the harness's own files (summary.md, samples.tsv, input_L*.txt, a0.wasm and
  a1.wasm, which the directory's .gitignore keeps out of git);
- host_samples.tsv: one row per second, phase (idle-check or run), total CPU
  percent and the compiler processes alive at that second;
- host_state.json: thresholds, the accepted idle window's mean/max, the
  during-run mean/max/n, the pinned CPU, the priority set, machine facts, the
  harness path, its SHA-256 and exit code, and the exact argv;
- harness_stdout.txt: the harness's stdout and stderr.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
import platform
import subprocess
import sys
import time
from pathlib import Path

try:
    import psutil
except ImportError:  # fail closed: without psutil there is no load sampling
    sys.exit(
        "quiet_run.py needs psutil (`python -m pip install psutil`): the idle "
        "precondition and the during-run load log are what make a run publishable"
    )

REPO_ROOT = Path(__file__).resolve().parents[2]

# Any of these alive during the idle window or the run disqualifies it: they
# are the processes that contend for the CPU and the memory bus on this host.
COMPILER_PROCESSES = frozenset(
    {"cargo", "rustc", "rustdoc", "clippy-driver", "lean", "lake"}
)

# Windows process-creation flag: start suspended so affinity and priority are
# in place before the harness executes its first instruction.
CREATE_SUSPENDED = 0x0000_0004


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def find_harness(explicit: str | None) -> Path:
    """The release harness binary, or a closed failure naming the build command."""
    if explicit is not None:
        path = Path(explicit)
        if not path.is_file():
            sys.exit(f"--harness {path}: no such file")
        return path.resolve()
    target = Path(os.environ.get("CARGO_TARGET_DIR", REPO_ROOT / "target"))
    exe = "fuel_overhead.exe" if os.name == "nt" else "fuel_overhead"
    candidates = [target / "release" / "examples" / exe]
    candidates += sorted(target.glob(f"*/release/examples/{exe}"))
    found = [p for p in candidates if p.is_file()]
    if not found:
        sys.exit(
            "no release harness found under "
            f"{target} (looked for release/examples/{exe} and */release/examples/{exe}).\n"
            "Build it first, on its own:\n"
            "    cargo build --release --no-default-features -p sigil-runtime "
            "--example fuel_overhead\n"
            "then run this script again (or pass --harness PATH)."
        )
    # Several target triples may hold a build; the newest is the one just built.
    return max(found, key=lambda p: p.stat().st_mtime).resolve()


def cpu_freq_mhz() -> dict | None:
    """What the OS reports as the current/max CPU clock, or None where it reports nothing.

    Informational: on Windows this is WMI's CurrentClockSpeed, which tracks the
    package clock coarsely and records no turbo state. It is recorded so a run
    taken under a clock cap is distinguishable from one taken without (the five
    capped 2026-09-30 runs record 3203 of 3504 MHz, the full-clock run 3504 of
    3504); the load numbers alone would not show that, and this figure does not
    show the effective clock either.
    """
    try:
        f = psutil.cpu_freq()
    except (psutil.Error, OSError, NotImplementedError):
        return None
    if f is None:
        return None
    return {"current": round(f.current, 1), "max": round(f.max, 1)}


def harness_label(harness: Path) -> str:
    """Repo-relative when the binary is inside the repo, else its file name only.

    An absolute path outside the repository is a host identifier (user names,
    drive letters) and must not land in a file that ships; the SHA-256 beside it
    is what identifies the binary.
    """
    try:
        return harness.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return harness.name


def compiler_processes() -> list[str]:
    names: list[str] = []
    for proc in psutil.process_iter(["name"]):
        name = proc.info.get("name") or ""
        stem = name.lower()
        if stem.endswith(".exe"):
            stem = stem[:-4]
        if stem in COMPILER_PROCESSES:
            names.append(stem)
    return sorted(names)


def sample_once(phase: str, t0: float, rows: list[dict]) -> dict:
    """One second of total CPU load plus the compiler processes alive now."""
    cpu = psutil.cpu_percent(interval=1.0)
    row = {
        "phase": phase,
        "t_s": round(time.monotonic() - t0, 1),
        "cpu_pct": cpu,
        "compiler_procs": compiler_processes(),
    }
    rows.append(row)
    return row


def wait_for_idle(args: argparse.Namespace, rows: list[dict], t0: float) -> dict:
    """Block until one full window meets the thresholds; fail closed at --max-wait."""
    deadline = time.monotonic() + args.max_wait
    attempt = 0
    while True:
        attempt += 1
        window = [sample_once("idle-check", t0, rows) for _ in range(args.idle_seconds)]
        loads = [r["cpu_pct"] for r in window]
        mean = sum(loads) / len(loads)
        peak = max(loads)
        procs = sorted({p for r in window for p in r["compiler_procs"]})
        ok = mean < args.idle_mean and peak < args.idle_max and not procs
        print(
            f"idle window {attempt}: mean {mean:.1f}% max {peak:.1f}% "
            f"compiler procs {procs or 'none'} -> {'ACCEPTED' if ok else 'rejected'}",
            flush=True,
        )
        if ok:
            return {
                "attempts": attempt,
                "seconds": args.idle_seconds,
                "mean_pct": round(mean, 2),
                "max_pct": round(peak, 2),
            }
        if time.monotonic() >= deadline:
            # Fail closed: a contended host measures the host, not the harness.
            sys.exit(
                f"host never idle within {args.max_wait} s "
                f"(last window: mean {mean:.1f}%, max {peak:.1f}%, procs {procs or 'none'}); "
                "not running the harness. Nothing to publish."
            )


def pin_and_raise(proc: psutil.Process, cpu: int) -> str:
    """Pin to one logical CPU and raise priority; fail closed if either is refused."""
    try:
        proc.cpu_affinity([cpu])
    except (psutil.Error, OSError, ValueError) as e:
        proc.kill()
        sys.exit(f"could not pin the harness to CPU {cpu}: {e}")
    try:
        if os.name == "nt":
            proc.nice(psutil.HIGH_PRIORITY_CLASS)
            return "HIGH_PRIORITY_CLASS"
        proc.nice(-10)
        return "nice -10"
    except (psutil.Error, OSError) as e:
        proc.kill()
        sys.exit(f"could not raise the harness's priority: {e}")


def run_harness(
    harness: Path, harness_args: list[str], out: Path, cpu: int, rows: list[dict], t0: float
) -> tuple[int, str, list[dict]]:
    argv = [str(harness), "--out", str(out), *harness_args]
    stdout_path = out / "harness_stdout.txt"
    creationflags = 0
    if os.name == "nt":
        creationflags = subprocess.HIGH_PRIORITY_CLASS | CREATE_SUSPENDED
    with stdout_path.open("w", encoding="utf-8", newline="\n") as log:
        child = subprocess.Popen(
            argv,
            cwd=REPO_ROOT,
            stdout=log,
            stderr=subprocess.STDOUT,
            creationflags=creationflags,
        )
        proc = psutil.Process(child.pid)
        priority = pin_and_raise(proc, cpu)
        if os.name == "nt":
            proc.resume()
        run_rows: list[dict] = []
        while child.poll() is None:
            run_rows.append(sample_once("run", t0, rows))
        # One more second so the tail of the run is in the log too.
        run_rows.append(sample_once("run", t0, rows))
    return child.returncode, priority, run_rows


def write_outputs(out: Path, rows: list[dict], state: dict) -> None:
    with (out / "host_samples.tsv").open("w", encoding="utf-8", newline="\n") as f:
        f.write("# total CPU load sampled once per second by bench/fuel-overhead/quiet_run.py\n")
        f.write("# compiler_procs: comma-joined names alive at that second, `-` when none\n")
        f.write("phase\tt_s\tcpu_pct\tcompiler_procs\n")
        for r in rows:
            # `-` rather than an empty field: an empty last field is a trailing tab,
            # which `git diff --check` in the hygiene lane refuses.
            procs = ",".join(r["compiler_procs"]) or "-"
            f.write(f"{r['phase']}\t{r['t_s']}\t{r['cpu_pct']}\t{procs}\n")
    with (out / "host_state.json").open("w", encoding="utf-8", newline="\n") as f:
        json.dump(state, f, indent=2, sort_keys=True)
        f.write("\n")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument(
        "--out",
        default=None,
        help="output directory (default bench/fuel-overhead/<YYYY-MM-DD>-idle, repo-relative)",
    )
    ap.add_argument("--harness", default=None, help="release harness binary (default: newest under the target dir)")
    ap.add_argument(
        "--cpu",
        type=int,
        default=psutil.cpu_count() - 1,
        help="logical CPU to pin the harness to (default: the last one, away from CPU 0's interrupts)",
    )
    ap.add_argument("--idle-seconds", type=int, default=60, help="length of the idle window (default 60)")
    ap.add_argument("--idle-mean", type=float, default=5.0, help="window mean load must be below this %% (default 5)")
    ap.add_argument("--idle-max", type=float, default=15.0, help="window peak load must be below this %% (default 15)")
    ap.add_argument("--max-wait", type=int, default=1200, help="give up after this many seconds not idle (default 1200)")
    ap.add_argument("harness_args", nargs="*", help="passed to the harness after `--` (e.g. --seed N --lengths 0,100)")
    args = ap.parse_args()

    harness = find_harness(args.harness)
    if args.out is None:
        out = REPO_ROOT / "bench" / "fuel-overhead" / f"{dt.date.today().isoformat()}-idle"
    else:
        out = Path(args.out)
        if not out.is_absolute():
            out = REPO_ROOT / out
    out.mkdir(parents=True, exist_ok=True)
    if not 0 <= args.cpu < psutil.cpu_count():
        sys.exit(f"--cpu {args.cpu} is not a logical CPU on this host (0..{psutil.cpu_count() - 1})")

    print(f"harness {harness}\n  sha256 {sha256_file(harness)}\nout {out}\npin CPU {args.cpu}", flush=True)
    rows: list[dict] = []
    t0 = time.monotonic()
    psutil.cpu_percent(interval=None)  # prime the counter; the first reading is meaningless
    started_at = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    freq_before = cpu_freq_mhz()
    idle = wait_for_idle(args, rows, t0)

    run_started = time.monotonic()
    code, priority, run_rows = run_harness(harness, args.harness_args, out, args.cpu, rows, t0)
    wall = time.monotonic() - run_started
    freq_after = cpu_freq_mhz()
    loads = [r["cpu_pct"] for r in run_rows]
    procs = sorted({p for r in run_rows for p in r["compiler_procs"]})
    state = {
        "runner": "bench/fuel-overhead/quiet_run.py",
        "started_utc": started_at,
        "thresholds": {
            "idle_seconds": args.idle_seconds,
            "idle_mean_pct_below": args.idle_mean,
            "idle_max_pct_below": args.idle_max,
            "max_wait_s": args.max_wait,
            "disqualifying_processes": sorted(COMPILER_PROCESSES),
        },
        "idle_window_accepted": idle,
        "during_run": {
            "n_samples": len(loads),
            "mean_pct": round(sum(loads) / len(loads), 2) if loads else None,
            "max_pct": max(loads) if loads else None,
            "samples_over_15_pct": sum(1 for x in loads if x >= 15.0),
            "compiler_procs_seen": procs,
            "wall_s": round(wall, 1),
        },
        "pinned_cpu": args.cpu,
        "priority": priority,
        "host": {
            "platform": platform.platform(),
            "processor": platform.processor(),
            "logical_cpus": psutil.cpu_count(),
            "physical_cores": psutil.cpu_count(logical=False),
            "python": platform.python_version(),
            "psutil": psutil.__version__,
            "cpu_freq_mhz_before_idle_check": freq_before,
            "cpu_freq_mhz_after_run": freq_after,
        },
        "harness": {
            "path": harness_label(harness),
            "sha256": sha256_file(harness),
            "argv_after_out": args.harness_args,
            "exit_code": code,
        },
    }
    write_outputs(out, rows, state)
    print(
        f"run: {wall:.0f} s, load mean {state['during_run']['mean_pct']}% max {state['during_run']['max_pct']}% "
        f"({state['during_run']['samples_over_15_pct']} of {len(loads)} samples >= 15%), "
        f"compiler procs {procs or 'none'}, harness exit {code}",
        flush=True,
    )
    if code != 0:
        # Fail closed: the samples are on disk for diagnosis, but there is no result.
        print(f"harness exited {code}; see {out / 'harness_stdout.txt'}. Not a publishable run.", file=sys.stderr)
        return 1
    if procs:
        print("a compiler process was alive during the run; the host_state.json says so.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
