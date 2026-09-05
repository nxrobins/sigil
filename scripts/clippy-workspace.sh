#!/usr/bin/env bash
set -euo pipefail

# `cargo clippy --all-targets` creates one frontend unit per integration-test
# crate. SIGIL currently has hundreds of those units. On high-core hosts, using
# every logical CPU makes all of them contend for the same dependency metadata
# and filesystem, increasing wall time while Cargo emits no target-level output.
# Keep the coverage exact, cap only excessive implicit parallelism, and provide
# a heartbeat so a live frontend phase is distinguishable from a stalled job.
CLIPPY_JOB_CAP=8
HEARTBEAT_SECONDS=30

is_positive_integer() {
  [[ "$1" =~ ^[1-9][0-9]*$ ]]
}

select_jobs() {
  local detected="$1"
  local requested="$2"

  if [[ -n "$requested" ]]; then
    if ! is_positive_integer "$requested"; then
      echo "SIGIL_CLIPPY_JOBS must be a positive integer, found: $requested" >&2
      return 2
    fi
    echo "$requested"
    return
  fi

  if ! is_positive_integer "$detected"; then
    detected=1
  fi
  if ((detected > CLIPPY_JOB_CAP)); then
    echo "$CLIPPY_JOB_CAP"
  else
    echo "$detected"
  fi
}

self_test() {
  [[ "$(select_jobs 32 "")" == "8" ]]
  [[ "$(select_jobs 4 "")" == "4" ]]
  [[ "$(select_jobs nonsense "")" == "1" ]]
  [[ "$(select_jobs 32 3)" == "3" ]]
  if select_jobs 8 0 >/dev/null 2>&1; then
    echo "clippy runner self-test accepted a zero job override" >&2
    return 1
  fi
}

run_with_heartbeat() {
  local label="$1"
  shift
  local started=$SECONDS

  echo "[clippy] start: $label (jobs=$jobs)"
  (
    while sleep "$HEARTBEAT_SECONDS"; do
      echo "[clippy] active: $label ($((SECONDS - started))s elapsed)"
    done
  ) &
  local heartbeat_pid=$!

  set +e
  "$@"
  local status=$?
  set -e

  kill "$heartbeat_pid" 2>/dev/null || true
  wait "$heartbeat_pid" 2>/dev/null || true
  if ((status != 0)); then
    echo "[clippy] failed: $label (status=$status, $((SECONDS - started))s elapsed)" >&2
    return "$status"
  fi
  echo "[clippy] complete: $label ($((SECONDS - started))s elapsed)"
}

self_test

mode="${1:-all}"
if [[ "$mode" == "self-test" ]]; then
  echo "clippy workspace runner self-test passed"
  exit 0
fi

detected_jobs="$(getconf _NPROCESSORS_ONLN 2>/dev/null || true)"
jobs="$(select_jobs "$detected_jobs" "${SIGIL_CLIPPY_JOBS:-}")"

run_no_default() {
  run_with_heartbeat "workspace, no default features" \
    cargo clippy --workspace --all-targets --no-default-features --locked \
      --jobs "$jobs" -- -D warnings
}

run_json() {
  run_with_heartbeat "sigil-compiler, json feature" \
    cargo clippy -p sigil-compiler --all-targets --no-default-features --features json --locked \
      --jobs "$jobs" -- -D warnings
}

case "$mode" in
  no-default)
    run_no_default
    ;;
  json)
    run_json
    ;;
  all)
    run_no_default
    run_json
    ;;
  *)
    echo "usage: $0 [all|no-default|json|self-test]" >&2
    exit 2
    ;;
esac
