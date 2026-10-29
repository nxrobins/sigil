#!/usr/bin/env bash
# Evict the hosted runner's preinstalled tooling in the BACKGROUND, and join on
# that eviction before the first step that needs the space.
#
# WHY. Every lane that builds the Lean-linked test binaries first deletes the
# SDKs nothing in this repository uses (Android, .NET, GHC, ...). As a serial
# step that `rm -rf` measured 146-251 s per lane on ci.yml's `test`, `checks`
# and `solver` (run 37142337416) and 232 s on a warm pull-request `test` run
# (37227497795): 13% of a 30-minute critical path spent waiting for deletions
# whose only consumer is the cargo build several steps later. `start` detaches
# the deletions so they overlap the toolchain installs and the cache restore;
# `wait` is the join.
#
# FAIL CLOSED, in both directions. A build that outruns the eviction dies as
# "No space left on device" or a linker SIGBUS, which reads like a broken link
# line (see the `test` job's disk-evidence step). So `wait` refuses to return
# until the worker has written its done-marker, refuses as soon as the worker
# reports a failed deletion, refuses when the worker is gone without a marker,
# and refuses if no marker appears within the timeout -- a lane that forgot
# `start`, or a worker that died, surfaces here by name instead of in the middle
# of a link. The worker writes the done-marker after its last deletion, so the
# marker means the deletions finished, not that they were requested; it writes
# the failed-marker at the first failed deletion, so a failure is never hidden
# behind the paths after it. `start` records the worker's pid, which is how a
# dead worker is told from a slow one.
#
# OR ENOUGH SPACE, when the lane says how much it needs. The deletions are a
# means to free space, and how long they take swings with the runner's disk: the
# `test` job's join measured 0-429 s over 25 runs (2026-10-07/08), and on run
# 37685207144 the worker was still on its 13th of 18 paths after 600 s, so the
# join refused with 42G already free against the ~33-35G the build adds. Given
# MIN_FREE_GB, `wait` also returns once THIS job's worker is running and `/`
# measures at least that many GiB available, leaving the worker to finish behind
# the build (it only ever frees more). Space that cannot be measured never
# counts: the join falls back to the done-marker. A failed deletion reported
# before the measurement, and a dead worker, still refuse, and without
# MIN_FREE_GB nothing changes. A lane that joins on free space must join again
# WITHOUT it before anything that needs the eviction finished or its failures
# reported (the `test` job does, before its tests).
#
# The worker's stdout/stderr go to a log file, never the step's pipes: a
# background process still holding those pipes makes the runner wait for it,
# which is the serial behaviour this replaces. Each log line carries the
# worker's elapsed seconds, so a slow eviction names its slow path.
#
# Usage:
#   free-runner-disk.sh start [--docker-prune] PATH...       # detach; returns at once
#   free-runner-disk.sh wait [TIMEOUT_SECONDS [MIN_FREE_GB]] # join; default 600, no space rule
#   free-runner-disk.sh --self-test                          # prove the refusals fire
#
# Environment (the self-test sets these; the lanes set none):
#   FREE_DISK_STATE_DIR  where the log and markers live (default: $RUNNER_TEMP, else /tmp)
#   FREE_DISK_SUDO       command prefixed to each deletion (default: sudo; empty = none)
#   FREE_DISK_AVAIL_CMD  command printing the GiB available on / (default: measured with df)
set -euo pipefail

state_dir="${FREE_DISK_STATE_DIR:-${RUNNER_TEMP:-/tmp}}"
log_file="$state_dir/free-runner-disk.log"
done_marker="$state_dir/free-runner-disk.done"
failed_marker="$state_dir/free-runner-disk.failed"
started_marker="$state_dir/free-runner-disk.started"
# `${VAR-default}`: unset means sudo, set-but-empty means no prefix at all.
sudo_cmd="${FREE_DISK_SUDO-sudo}"
default_timeout=600

# At most six digits: a timeout or a GiB figure past that is a typo, and a
# longer one would overflow bash arithmetic into a negative bound.
is_positive_integer() {
  [[ "$1" =~ ^[1-9][0-9]{0,5}$ ]]
}

# The whole GiB available on /, rounded DOWN, or a nonzero status when it cannot
# be measured (no df, an unexpected format): the caller then treats the space as
# unknown, never as enough.
available_gib() {
  local out
  if [[ -n "${FREE_DISK_AVAIL_CMD:-}" ]]; then
    out="$(bash -c "$FREE_DISK_AVAIL_CMD" 2> /dev/null)" || return 1
    [[ "$out" =~ ^[0-9]+$ ]] || return 1
    echo "$out"
    return 0
  fi
  out="$(df -k --output=avail / 2> /dev/null | tail -n 1)" || return 1
  out="${out//[[:space:]]/}"
  [[ "$out" =~ ^[0-9]+$ ]] || return 1
  echo $((out / 1048576))
}

# 0 = the worker `start` recorded is running, 1 = it is gone, 2 = no worker is
# recorded (no `start`, or an unreadable pid).
worker_status() {
  local pid
  pid="$(cat "$started_marker" 2> /dev/null)" || return 2
  [[ "$pid" =~ ^[1-9][0-9]*$ ]] || return 2
  if kill -0 "$pid" 2> /dev/null; then
    return 0
  fi
  return 1
}

start() {
  local docker_prune=0
  if [[ "${1:-}" == "--docker-prune" ]]; then
    docker_prune=1
    shift
  fi
  if (($# == 0)); then
    echo "free-runner-disk: start needs at least one path to evict" >&2
    return 2
  fi
  mkdir -p "$state_dir"
  rm -f "$done_marker" "$failed_marker" "$started_marker"
  : > "$log_file"
  # The worker. `nohup` with stdin, stdout and stderr all redirected, then
  # `disown`: it survives the end of the step and holds none of its pipes. The
  # arguments after `_` become the worker's "$@". `${sudo_cmd:+"$sudo_cmd"}`
  # contributes no word at all when the prefix is empty.
  # shellcheck disable=SC2016  # the worker body is a literal; its expansions run inside the worker
  nohup bash -c '
    set -u
    sudo_cmd="$1"; docker_prune="$2"; done_marker="$3"; failed_marker="$4"; shift 4
    status=0
    for path in "$@"; do
      if ${sudo_cmd:+"$sudo_cmd"} rm -rf -- "$path"; then
        echo "evicted: $path (${SECONDS}s)"
      else
        echo "FAILED to evict: $path (${SECONDS}s)"
        status=1
        # Reported now, not after the paths that follow: a join must not read a
        # failure that already happened as an eviction still under way.
        : > "$failed_marker"
      fi
    done
    if [ "$docker_prune" = 1 ]; then
      # Best effort by decision: the images are a bonus on top of the SDK
      # deletions, which are the load-bearing part, and an image without a
      # docker daemon is not an eviction failure. Say so in the log either way.
      if ${sudo_cmd:+"$sudo_cmd"} docker image prune --all --force > /dev/null 2>&1; then
        echo "pruned: docker images (${SECONDS}s)"
      else
        echo "note: docker image prune did not run, not an eviction failure (${SECONDS}s)"
      fi
    fi
    if [ "$status" = 0 ]; then : > "$done_marker"; fi
  ' _ "$sudo_cmd" "$docker_prune" "$done_marker" "$failed_marker" "$@" \
    < /dev/null > "$log_file" 2>&1 &
  # The pid lets `wait` tell a dead worker from a slow one. `nohup` execs its
  # command, so this is the worker itself.
  echo "$!" > "$started_marker"
  disown
  echo "free-runner-disk: evicting $# path(s) in the background; join with \`$0 wait\` before the first build step"
}

wait_for_eviction() {
  local timeout="${1:-$default_timeout}"
  local min_free="${2:-}"
  if ! is_positive_integer "$timeout"; then
    echo "free-runner-disk: wait takes a positive integer timeout in seconds (at most 6 digits), found: $timeout" >&2
    return 2
  fi
  if [[ -n "$min_free" ]] && ! is_positive_integer "$min_free"; then
    echo "free-runner-disk: wait takes a positive integer MIN_FREE_GB (at most 6 digits), found: $min_free" >&2
    return 2
  fi
  local waited=0 avail="" worker
  while true; do
    if [[ -e "$failed_marker" ]]; then
      echo "free-runner-disk: the eviction reported a failed deletion:" >&2
      cat "$log_file" >&2
      return 1
    fi
    if [[ -e "$done_marker" ]]; then
      echo "free-runner-disk: eviction finished (joined after ${waited}s)"
      cat "$log_file"
      # Evidence, not a gate: the free-space figure the lanes used to print inline.
      df -h / || echo "free-runner-disk: df unavailable on this host (evidence line only)"
      return 0
    fi
    worker=0
    worker_status || worker=$?
    if ((worker == 1)); then
      # The worker writes its marker before it exits, so a gone worker without
      # one died; look once more in case it finished between the two checks.
      if [[ -e "$failed_marker" || -e "$done_marker" ]]; then
        continue
      fi
      echo "free-runner-disk: the eviction worker (pid $(cat "$started_marker")) exited without finishing." >&2
      echo "free-runner-disk: refusing to proceed onto a disk that may still be full." >&2
      if [[ -s "$log_file" ]]; then cat "$log_file" >&2; fi
      return 1
    fi
    # The space rule (see the header): only while this job's worker is running,
    # and only on a measured figure.
    if [[ -n "$min_free" ]] && ((worker == 0)); then
      if avail="$(available_gib)" && ((avail >= min_free)); then
        # A failure reported while measuring still wins.
        if [[ -e "$failed_marker" ]]; then
          continue
        fi
        echo "free-runner-disk: proceeding after ${waited}s on measured free space (${avail}G available, ${min_free}G required); the eviction has not finished, so join again without MIN_FREE_GB before anything that needs it finished"
        if [[ -s "$log_file" ]]; then cat "$log_file"; fi
        df -h / || echo "free-runner-disk: df unavailable on this host (evidence line only)"
        return 0
      fi
    fi
    if ((waited >= timeout)); then
      echo "free-runner-disk: no eviction finished within ${timeout}s (no marker under $state_dir)." >&2
      if [[ -n "$min_free" ]]; then
        echo "free-runner-disk: and the free space never measured ${min_free}G (last reading: ${avail:-none})." >&2
      fi
      echo "free-runner-disk: refusing to proceed onto a disk that may still be full -- was \`start\` called, and did its worker survive?" >&2
      if [[ -s "$log_file" ]]; then cat "$log_file" >&2; fi
      return 1
    fi
    sleep 1
    waited=$((waited + 1))
  done
}

fail() {
  echo "free-runner-disk self-test FAILED: $*" >&2
  exit 1
}

self_test() {
  local tmp self out rc
  tmp="$(mktemp -d)"
  # shellcheck disable=SC2064  # expand $tmp now: the trap must remove THIS run's directory
  trap "rm -rf '$tmp'" EXIT
  self="$0"
  export FREE_DISK_STATE_DIR="$tmp/state"
  export FREE_DISK_SUDO=""
  unset FREE_DISK_AVAIL_CMD

  # Every join below runs under `timeout`: a broken join that never returns must
  # fail its case (exit 124), not hang the lane until its job timeout.
  #
  # The pid of the worker the last `start` recorded, once it has exited: the
  # cases share one state directory, so no worker may outlive its case.
  drain() {
    local pid n=0
    pid="$(cat "$FREE_DISK_STATE_DIR/free-runner-disk.started")"
    while kill -0 "$pid" 2> /dev/null; do
      ((n < 60)) || fail "a worker (pid $pid) was still running after 60 s"
      sleep 1
      n=$((n + 1))
    done
  }

  # 0. The real measurement, which every lane that passes MIN_FREE_GB runs: df's
  #    figure must match an independent one (statfs through `stat -f`) to within a
  #    GiB, so a wrong column, unit or constant cannot hide behind the mocked
  #    readings the cases below use. Where `stat -f` cannot measure, the check is
  #    skipped by name -- except on CI, which runs it and must not skip it.
  local measured independent
  if independent="$(stat -f -c '%a %S' / 2> /dev/null)" \
    && [[ "$independent" =~ ^([0-9]+)\ ([0-9]+)$ ]]; then
    independent=$((BASH_REMATCH[1] * BASH_REMATCH[2] / 1073741824))
    measured="$(available_gib)" || fail "df could not measure the space on / although statfs could"
    ((measured - independent <= 1 && independent - measured <= 1)) \
      || fail "df measured ${measured}G available on /, statfs ${independent}G"
  elif [[ "${GITHUB_ACTIONS:-}" == true ]]; then
    fail "no independent measure of / (stat -f) on a CI runner"
  else
    echo "free-runner-disk self-test: skipping the df cross-check (no stat -f on this host)"
  fi

  # 1. A clean eviction: exactly the named paths are gone, a bystander survives,
  #    and the join returns 0.
  mkdir -p "$tmp/victim-a/deep" "$tmp/victim-b" "$tmp/bystander"
  : > "$tmp/victim-a/deep/file"
  : > "$tmp/victim-b/file"
  : > "$tmp/bystander/file"
  bash "$self" start "$tmp/victim-a" "$tmp/victim-b" > /dev/null
  timeout -k 5 60 bash "$self" wait 30 > /dev/null || fail "wait did not return 0 after a clean eviction"
  [[ ! -e "$tmp/victim-a" && ! -e "$tmp/victim-b" ]] || fail "an evicted path survived"
  [[ -e "$tmp/bystander/file" ]] || fail "a path that was not named was deleted"

  # 2. A join with nothing in flight fails closed: no marker, no proceed.
  rm -f "$FREE_DISK_STATE_DIR"/free-runner-disk.*
  rc=0
  out="$(timeout -k 5 60 bash "$self" wait 1 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"no eviction finished within 1s"* ]] \
    || fail "a join with nothing in flight did not refuse at its timeout: $out"

  # 3. A deletion the worker cannot perform is REPORTED, not swallowed. `rm`
  #    refuses a path ending in `/.` (POSIX requires it), everywhere, as any user.
  mkdir -p "$tmp/victim-c"
  : > "$tmp/victim-c/file"
  bash "$self" start "$tmp/victim-c/." > /dev/null
  rc=0
  out="$(timeout -k 5 60 bash "$self" wait 30 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"reported a failed deletion"* ]] \
    || fail "wait did not refuse an eviction whose deletion failed: $out"
  [[ -e "$tmp/victim-c/file" ]] || fail "the refused deletion removed the file anyway"
  drain

  # 4. Malformed invocations are refused by their own check (exit 2 and its
  #    message), from a clean state, so no marker can answer for the validator.
  rm -f "$FREE_DISK_STATE_DIR"/free-runner-disk.*
  rc=0
  out="$(bash "$self" start 2>&1)" || rc=$?
  ((rc == 2)) && [[ "$out" == *"at least one path"* ]] || fail "start accepted an empty path list: $out"
  for args in "zero" "1234567"; do
    rc=0
    # Under `timeout`: a validator that let 1234567 through would wait two weeks, so the case
    # must end on its own clock and fail, not hang the lane until its job timeout.
    out="$(timeout 20 bash "$self" wait $args 2>&1)" || rc=$?
    ((rc == 2)) && [[ "$out" == *"positive integer timeout"* ]] \
      || fail "wait accepted the timeout '$args' (exit $rc): $out"
  done
  for args in "5 zero" "5 1234567"; do
    rc=0
    # shellcheck disable=SC2086  # split on purpose: TIMEOUT and MIN_FREE_GB
    out="$(timeout -k 5 60 bash "$self" wait $args 2>&1)" || rc=$?
    ((rc == 2)) && [[ "$out" == *"positive integer MIN_FREE_GB"* ]] \
      || fail "wait accepted the arguments '$args': $out"
  done

  # 5-11: the space rule, against planted SLOW workers: a deletion of a path
  # whose name contains `slow` first sleeps 4 s, so no done-marker can exist
  # during the first joins below.
  local slow="$tmp/slow-rm"
  printf '#!/usr/bin/env bash\ncase "$*" in *slow*) sleep 4 ;; esac\nexec "$@"\n' > "$slow"
  chmod +x "$slow"

  # 5. Enough measured space joins at once, before the worker has finished, and
  #    says so; the worker then still completes its deletion.
  mkdir -p "$tmp/slow-d"
  FREE_DISK_SUDO="$slow" bash "$self" start "$tmp/slow-d" > /dev/null
  out="$(FREE_DISK_AVAIL_CMD="echo 100" timeout -k 5 60 bash "$self" wait 30 40)" \
    || fail "wait refused a slow eviction with 100G measured against 40G required"
  [[ "$out" == *"proceeding after"* ]] || fail "the space join did not say it proceeded on free space"
  [[ ! -e "$FREE_DISK_STATE_DIR/free-runner-disk.done" ]] \
    || fail "the space join waited for the worker, so it proves nothing about the space rule"
  timeout -k 5 60 bash "$self" wait 30 > /dev/null || fail "the slow worker did not finish after the space join"
  [[ ! -e "$tmp/slow-d" ]] || fail "the slow worker's path survived"

  # 6. Exactly the required space is enough.
  mkdir -p "$tmp/slow-e"
  FREE_DISK_SUDO="$slow" bash "$self" start "$tmp/slow-e" > /dev/null
  out="$(FREE_DISK_AVAIL_CMD="echo 40" timeout -k 5 60 bash "$self" wait 30 40)" \
    || fail "wait refused a slow eviction with exactly 40G measured against 40G required"
  [[ "$out" == *"proceeding after"* ]] || fail "the at-threshold join did not proceed on free space"
  timeout -k 5 60 bash "$self" wait 30 > /dev/null || fail "the slow worker did not finish after the at-threshold join"

  # 7. Too little measured space refuses at the timeout: the slow worker is the
  #    2026-10-07 failure, and with the space short the join must still say no.
  mkdir -p "$tmp/slow-f"
  FREE_DISK_SUDO="$slow" bash "$self" start "$tmp/slow-f" > /dev/null
  rc=0
  out="$(FREE_DISK_AVAIL_CMD="echo 39" timeout -k 5 60 bash "$self" wait 2 40 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"never measured 40G (last reading: 39)"* ]] \
    || fail "the short-space join did not refuse at its timeout: $out"
  timeout -k 5 60 bash "$self" wait 30 > /dev/null || fail "the slow worker did not finish after the refused join"

  # 8. Without MIN_FREE_GB there is no space rule, whatever the space: plenty
  #    measured, the slow worker still makes the join time out.
  mkdir -p "$tmp/slow-g"
  FREE_DISK_SUDO="$slow" bash "$self" start "$tmp/slow-g" > /dev/null
  rc=0
  out="$(FREE_DISK_AVAIL_CMD="echo 100" timeout -k 5 60 bash "$self" wait 2 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"no eviction finished within 2s"* ]] \
    || fail "a join without MIN_FREE_GB proceeded before the worker finished: $out"
  timeout -k 5 60 bash "$self" wait 30 > /dev/null || fail "the slow worker did not finish after the completion-only join"

  # 9. A failed deletion reported before the join wins over measured space: the
  #    first path fails at once, the second is slow, and the join must refuse
  #    on the failure rather than read the worker as still evicting.
  mkdir -p "$tmp/victim-h" "$tmp/slow-i"
  : > "$tmp/victim-h/file"
  FREE_DISK_SUDO="$slow" bash "$self" start "$tmp/victim-h/." "$tmp/slow-i" > /dev/null
  sleep 1
  rc=0
  out="$(FREE_DISK_AVAIL_CMD="echo 100" timeout -k 5 60 bash "$self" wait 10 40 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"reported a failed deletion"* ]] \
    || fail "a space join proceeded past a failed deletion: $out"
  drain

  # 10. Space never stands in for a missing start: nothing in flight refuses even
  #     with plenty measured.
  rm -f "$FREE_DISK_STATE_DIR"/free-runner-disk.*
  rc=0
  out="$(FREE_DISK_AVAIL_CMD="echo 100" timeout -k 5 60 bash "$self" wait 2 40 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"no eviction finished within 2s"* ]] \
    || fail "wait proceeded on free space with no eviction started: $out"

  # 11. Space that cannot be measured is unknown, not enough: the join falls back
  #     to the done-marker and refuses at the timeout.
  mkdir -p "$tmp/slow-j"
  FREE_DISK_SUDO="$slow" bash "$self" start "$tmp/slow-j" > /dev/null
  rc=0
  out="$(FREE_DISK_AVAIL_CMD="echo plenty" timeout -k 5 60 bash "$self" wait 2 40 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"no eviction finished within 2s"* ]] \
    || fail "wait proceeded on an unmeasurable free-space reading: $out"
  timeout -k 5 60 bash "$self" wait 30 > /dev/null || fail "the slow worker did not finish after the unmeasured join"

  # 12. A worker that died without a marker is refused by name, at once and with
  #     plenty of space, not left to the timeout or read as still evicting. The
  #     state is planted rather than made by killing a live worker: under Git
  #     Bash's process emulation a signal can miss a worker mid-exec, which would
  #     make this case flaky. Recorded pid: a process that has already exited.
  rm -f "$FREE_DISK_STATE_DIR"/free-runner-disk.*
  : > "$FREE_DISK_STATE_DIR/free-runner-disk.log"
  local gone
  bash -c 'exit 0' &
  gone=$!
  wait "$gone" || true
  echo "$gone" > "$FREE_DISK_STATE_DIR/free-runner-disk.started"
  rc=0
  out="$(FREE_DISK_AVAIL_CMD="echo 100" timeout -k 5 60 bash "$self" wait 30 40 2>&1)" || rc=$?
  ((rc == 1)) && [[ "$out" == *"exited without finishing"* ]] \
    || fail "a join on a dead worker did not refuse it by name: $out"

  echo "free-runner-disk self-test passed: df agrees with statfs, a clean eviction joins, missing, failed and dead evictions refuse, malformed calls refuse, a slow eviction joins on measured space only with MIN_FREE_GB, enough space measured and no failure reported, for a worker this job started"
}

case "${1:-}" in
  start)
    shift
    start "$@"
    ;;
  wait)
    shift
    wait_for_eviction "$@"
    ;;
  --self-test)
    self_test
    ;;
  *)
    echo "usage: $0 start [--docker-prune] PATH... | wait [TIMEOUT_SECONDS [MIN_FREE_GB]] | --self-test" >&2
    exit 2
    ;;
esac
