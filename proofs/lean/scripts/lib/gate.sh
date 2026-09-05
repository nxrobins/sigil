#!/usr/bin/env bash
# Shared fail-closed gate functions for a λ-SIGIL Lake package. Sourced, never run:
#   proofs/lean/scripts/check-no-sorry.sh           the public development
#   proofs/lean-research/scripts/check-no-sorry.sh  the research overlay that requires it
#
# A driver sets the readonly pins and package facts below, sources this file, installs
# `trap cleanup EXIT`, and runs the steps in order. Nothing here reads a pin the driver did not
# set, and every checker is fail-closed: it returns 0 only when it RAN and reported on every
# target (the public driver's header records the fail-open bug class this guards against).
#
# Driver-provided variables:
#   ROOT_MODULE            the Lake root module whose elaborated environment is censused
#   SOURCE_DIR             the module tree scanned for sorry/admit, native_decide, and orphans
#   AXIOM_TARGETS          the committed theorem manifest (newline-delimited, bytewise sorted)
#   AXIOM_ALLOWLIST        the committed allowed-axiom manifest
#   PIN_AXIOM_TARGETS      exact manifest cardinality
#   PIN_ALLOWED_AXIOMS     exact allowlist cardinality
#   PIN_NATIVE_DECIDE      exact count of kernel-external native_decide uses (0 unless legacy)
#   NATIVE_DECIDE_DIR      directory prefix the legacy uses are confined to ("" = none allowed)
#   CENSUS_MODULE_PREFIX   censused theorems must be declared in a module whose name has this
#                          prefix ("" = every theorem the environment carries). The overlay uses
#                          it to exclude the public package it imports; the public package needs
#                          no filter because it imports nothing but itself.
#   RAW_FORBIDDEN_DEPENDENCIES  the sanitized/assumed-policy symbol regex for the raw-claim audit

# Clean up the generated report files and any self-test scratch on ANY exit (incl. failure).
SELFTEST_TMP=""
CENSUS_LIST=""
cleanup() {
  rm -f AxCheckCI.lean CensusCI.lean RawClaimAuditCI.lean
  [ -n "$CENSUS_LIST" ] && rm -f "$CENSUS_LIST" || true
  [ -n "$SELFTEST_TMP" ] && rm -rf "$SELFTEST_TMP" || true
}

# Run a transitive declaration-graph audit for the production relational corollaries.  The helper
# walks elaborated declaration types and values through `Expr.getUsedConstants`; this catches an
# indirect dependency through an innocently named wrapper, which source-text greps cannot do.
check_raw_claim_dependencies() {
  local auditfile="$1" expected="$2" forbidden="$3" out rc=0
  out=$(lake env lean "$auditfile" 2>&1) || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAIL: raw claim dependency audit did not elaborate (lake env lean rc=$rc)" >&2
    return 1
  fi
  local reports dependencies
  reports=$(printf '%s\n' "$out" | grep -c '^RAWCLAIM|' || true)
  dependencies=$(printf '%s\n' "$out" | grep -c '^RAWDEP|' || true)
  if [ "$expected" -le 0 ] || [ "$reports" -ne "$expected" ] || [ "$dependencies" -le 0 ]; then
    echo "FAIL: raw claim dependency audit reported $reports/$expected claims and $dependencies dependencies" >&2
    return 1
  fi
  if printf '%s\n' "$out" | grep '^RAWDEP|' | grep -Eq "$forbidden"; then
    echo "FAIL: a production raw-relational claim transitively depends on a sanitized or assumed-policy symbol:" >&2
    printf '%s\n' "$out" | grep '^RAWDEP|' | grep -E "$forbidden" | head -20 >&2
    return 1
  fi
}

write_raw_claim_audit() {
  cat > "$1" <<'LEAN'
import LambdaSigil.RawClaimDependencyAudit

run_cmd do
  reportRawClaimDependencies (← Lean.getEnv)
    [`LambdaSigil.Combined.RawClaimSurface.secretCT_delimited_release_trace_equality,
     `LambdaSigil.Combined.RawClaimSurface.public_delimited_release_noninterference]
LEAN
}

# Derive the theorem census from Lean's ELABORATED ENVIRONMENT instead of from source text.
# This is the fence F-20-6 was missing.  A text parser can be blinded by declaration syntax: an
# attribute prefix hid `Label.le_refl` from the Rust source scraper, and therefore from this
# gate, because the manifest is compared against that scraper's own output -- so the theorem was
# absent from BOTH sides and the equality still held.  The environment cannot be blinded that
# way.  If Lean elaborated it as a theorem, it is here, whatever the source looked like.
# Five filters, each principled rather than a pattern guess:
#   .thmInfo                  theorems, not defs / instances / axioms
#   `LambdaSigil` prefix      this development (also drops `_private.*` mangled names)
#   not internal, not a projection
#                             drops compiler-generated `.eq_n` / `.injEq` / `.sizeOf_spec`, and
#                             the Prop-valued structure field projections (152 of them)
#   has a declaration range   drops anything with no source position
#   declaring module prefix   (CENSUS_MODULE_PREFIX, optional) the package's OWN modules, so an
#                             overlay does not re-census the package it imports
write_census_ci() {
  # A quoted heredoc into a scratch file, then a substitution pass: the Lean template carries
  # backticks (name literals), which a heredoc inside `$(...)` does not survive on every bash.
  local template
  template=$(mktemp)
  cat > "$template" <<'LEAN'
import __ROOT__
open Lean

run_cmd do
  let env ← Lean.getEnv
  let mods := env.header.moduleNames
  let modulePrefix : String := "__PREFIX__"
  let mut out : Array String := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo _ =>
        if (`LambdaSigil).isPrefixOf n && !(isPrivateName n) && !n.isInternal then
          if (← findDeclarationRanges? n).isSome && !(← isProjectionFn n) then
            let inScope :=
              if modulePrefix.isEmpty then true else
                match env.getModuleIdxFor? n with
                | some idx => (mods[idx.toNat]!).toString.startsWith modulePrefix
                | none => false
            if inScope then
              out := out.push (n.toString.drop "LambdaSigil.".length).toString
    | _ => pure ()
  for s in out.qsort (· < ·) do IO.println s!"CENSUS|{s}"
LEAN
  sed -e "s/__ROOT__/$ROOT_MODULE/" -e "s/__PREFIX__/$CENSUS_MODULE_PREFIX/" "$template" > "$1"
  rm -f "$template"
}

# Run the environment census into a sorted identifier list. Fail-closed on a non-elaborating
# file AND on empty output -- an empty census must never read as "nothing to check", which is
# exactly the fail-open shape this gate exists to prevent.
run_census() {
  local censusfile="$1" outfile="$2" out rc=0
  out=$(lake env lean "$censusfile" 2>&1) || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAIL: environment census did not elaborate (lake env lean rc=$rc)" >&2
    return 1
  fi
  printf '%s\n' "$out" | sed -n 's/^CENSUS|//p' | LC_ALL=C sort > "$outfile"
  if [ ! -s "$outfile" ]; then
    echo "FAIL: environment census reported no theorems -- it did not actually run" >&2
    return 1
  fi
}

# Compare the environment census to the committed manifest. A difference either way fails: an
# extra means a theorem escaped the manifest and so escaped the axiom check (F-20-6's shape);
# a missing means the manifest names something the environment does not carry.
compare_census() {
  local census="$1" manifest="$2" sorted extra missing
  sorted=$(mktemp)
  LC_ALL=C sort "$manifest" > "$sorted"
  extra=$(LC_ALL=C comm -23 "$census" "$sorted" || true)
  missing=$(LC_ALL=C comm -13 "$census" "$sorted" || true)
  rm -f "$sorted"
  if [ -n "$extra" ]; then
    echo "FAIL: elaborated theorems missing from the manifest (they escape the axiom check):" >&2
    printf '%s\n' "$extra" | head -20 >&2
    return 1
  fi
  if [ -n "$missing" ]; then
    echo "FAIL: manifest names theorems the elaborated environment does not carry:" >&2
    printf '%s\n' "$missing" | head -20 >&2
    return 1
  fi
}

# Scan Lean sources for `sorry`/`admit`. Returns 0 only when the scan RAN and found nothing.
# Fail-closed on a missing target and on a grep ERROR (rc>=2), not just on a match (rc==0).
scan_sorry_admit() {
  local t
  for t in "$@"; do
    if [ ! -e "$t" ]; then
      echo "FAIL: sorry/admit scan target '$t' is missing (sources moved/renamed?)" >&2
      return 1
    fi
  done
  local rc=0
  # Match `sorry`/`admit` as code, not when backtick-quoted inside doc comments.
  # shellcheck disable=SC2016  # Single quotes preserve regex anchors literally.
  grep -rnE '(^|[^`[:alnum:]])(sorry|admit)([^`[:alnum:]]|$)' "$@" || rc=$?
  # grep rc: 0 = a token was found, 1 = clean, >=2 = grep itself errored.
  if [ "$rc" -eq 0 ]; then
    echo "FAIL: found sorry/admit in sources" >&2
    return 1
  elif [ "$rc" -ge 2 ]; then
    echo "FAIL: sorry/admit scan could not run (grep rc=$rc)" >&2
    return 1
  fi
  return 0
}

# `native_decide` leaves the kernel -- it trusts the compiler's evaluator instead of checking a
# proof term -- so no THEOREM may use it. A package may carry a pinned count of legacy anonymous
# `example` witnesses confined to NATIVE_DECIDE_DIR (the research overlay's first campaign has
# seventeen); a public package pins zero and confines nothing. A new use ANYWHERE fails the gate.
# Named theorems are additionally fenced by the axiom check: native_decide surfaces
# `Lean.ofReduceBool`, which is not allowlisted.
scan_native_decide() {
  local expected="$1"
  shift
  local t
  for t in "$@"; do
    if [ ! -e "$t" ]; then
      echo "FAIL: native_decide scan target '$t' is missing (sources moved/renamed?)" >&2
      return 1
    fi
  done
  local out rc=0
  # shellcheck disable=SC2016  # Single quotes preserve regex anchors literally.
  out=$(grep -rhoE '(^|[^`[:alnum:]])(native_decide)([^`[:alnum:]]|$)' "$@") || rc=$?
  if [ "$rc" -ge 2 ]; then
    echo "FAIL: native_decide scan could not run (grep rc=$rc)" >&2
    return 1
  fi
  local got
  got=$(printf '%s' "$out" | grep -c . || true)
  if [ "$got" -ne "$expected" ]; then
    echo "FAIL: found $got native_decide uses; pinned legacy count is $expected" >&2
    echo "      native_decide leaves the kernel -- a new use is not allowed" >&2
    return 1
  fi
  if [ -n "${NATIVE_DECIDE_DIR:-}" ]; then
    local stray
    # shellcheck disable=SC2016  # Single quotes preserve regex anchors literally.
    stray=$(grep -rlE '(^|[^`[:alnum:]])(native_decide)([^`[:alnum:]]|$)' "$@" \
      | grep -cv "^${NATIVE_DECIDE_DIR}" || true)
    if [ "$stray" -ne 0 ]; then
      echo "FAIL: native_decide appears outside the pinned legacy directory ${NATIVE_DECIDE_DIR}" >&2
      return 1
    fi
  fi
}

# The environment census sees only what the ROOT IMPORTS. This closes the complement, and does
# it without a pin to maintain: every file outside the root's transitive import closure must
# declare nothing provable.
#
# "Just import everything" is NOT available as a fix -- the fourteen standalone emitters each
# define `main`, and two `main`s in one import graph clash, which is exactly why they sit outside
# the closure. They are `def main` files carrying no `theorem`/`lemma` token at all, so nothing
# provable lives where the census cannot look.
#
# Together the two rules end the escape class rather than chasing it: an IMPORTED file is covered
# by the environment census whatever its declaration syntax (attribute-prefixed, `lemma`,
# `noncomputable`, or any form Lean grows later), and an UNIMPORTED file may not carry a theorem
# in the first place. Token-level matching is deliberate -- every theorem-producing form contains
# `theorem` or `lemma`, so this needs no list of modifier keywords to keep current.
scan_unimported_are_proof_free() {
  local rootmod="$1" dir="$2"
  local work seen closure ondisk mod path offenders
  work=$(mktemp); seen=$(mktemp); closure=$(mktemp); ondisk=$(mktemp)
  printf '%s\n' "$rootmod" > "$work"
  while [ -s "$work" ]; do
    mod=$(head -n 1 "$work")
    tail -n +2 "$work" > "$work.rest" && mv "$work.rest" "$work"
    if grep -Fxq "$mod" "$seen"; then continue; fi
    printf '%s\n' "$mod" >> "$seen"
    path="$(printf '%s' "$mod" | tr '.' '/').lean"
    [ -f "$path" ] || continue
    grep -oE "^import[[:space:]]+${rootmod}[A-Za-z0-9_.]*" "$path" | awk '{print $2}' >> "$work" \
      || true
  done
  while IFS= read -r mod; do
    printf '%s\n' "$(printf '%s' "$mod" | tr '.' '/').lean"
  done < "$seen" | LC_ALL=C sort > "$closure"
  { find "$dir" -name '*.lean'; printf '%s\n' "$rootmod.lean"; } | LC_ALL=C sort > "$ondisk"
  offenders=""
  while IFS= read -r file; do
    [ -f "$file" ] || continue
    if grep -Fxq "$file" "$closure"; then continue; fi
    # shellcheck disable=SC2016  # Single quotes preserve regex anchors literally.
    if grep -qE '(^|[^`[:alnum:]_])(theorem|lemma)([^`[:alnum:]_]|$)' "$file"; then
      offenders="${offenders}      ${file}"$'\n'
    fi
  done < "$ondisk"
  rm -f "$work" "$work.rest" "$seen" "$closure" "$ondisk"
  if [ -n "$offenders" ]; then
    echo "FAIL: a file outside the root import closure declares something provable." >&2
    echo "      The environment census cannot see unimported modules, so this would be" >&2
    echo "      checked by nothing. Import it, or move the proof into an imported module:" >&2
    printf '%s' "$offenders" >&2
    return 1
  fi
}

# Validate a newline-delimited identifier manifest without trusting generated Lean input. The
# fixed cardinality makes deletion fail even when both the manifest and generated report agree.
validate_identifier_manifest() {
  local manifest="$1" expected="$2" label="$3"
  if [ ! -f "$manifest" ]; then
    echo "FAIL: $label manifest '$manifest' is missing" >&2
    return 1
  fi
  # Lean permits `?` in declaration identifiers (for example a lemma about `getElem?`).
  # Keep the accepted alphabet explicit so manifest text still cannot inject commands into the
  # generated `#print axioms` file.
  if grep -nEv '^[A-Za-z_][A-Za-z0-9_.?]*$' "$manifest" >&2; then
    echo "FAIL: $label manifest contains a blank, comment, or invalid identifier" >&2
    return 1
  fi
  local count unique_count
  count=$(wc -l < "$manifest" | tr -d '[:space:]')
  unique_count=$(LC_ALL=C sort -u "$manifest" | wc -l | tr -d '[:space:]')
  if [ "$count" -ne "$expected" ]; then
    echo "FAIL: $label manifest has $count entries; pinned count is $expected" >&2
    return 1
  fi
  if [ "$unique_count" -ne "$count" ]; then
    echo "FAIL: $label manifest contains duplicate identifiers" >&2
    return 1
  fi
  if ! LC_ALL=C sort "$manifest" | cmp -s - "$manifest"; then
    echo "FAIL: $label manifest must remain bytewise sorted" >&2
    return 1
  fi
}

validate_allowlist() {
  local allowlist="$1"
  validate_identifier_manifest "$allowlist" "$PIN_ALLOWED_AXIOMS" "allowed-axiom" || return 1
  local expected
  for expected in Classical.choice Quot.sound propext; do
    if ! grep -Fxq "$expected" "$allowlist"; then
      echo "FAIL: allowed-axiom manifest lost pinned entry '$expected'" >&2
      return 1
    fi
  done
}

# Generate the Lean report from the independently committed target inventory. Names are
# manifest-relative under `LambdaSigil`, whichever package declared them.
write_axcheck() {
  local outfile="$1" targets="$2"
  {
    printf 'import %s\nopen LambdaSigil\n' "$ROOT_MODULE"
    while IFS= read -r target; do
      printf '#print axioms %s\n' "$target"
    done < "$targets"
  } > "$outfile"
}

# Run an axiom-report file and return 0 only if it (a) ELABORATED, (b) reported on EVERY
# independently expected target, and (c) named only allowlisted axioms. Any failure is closed.
check_axioms() {
  local axfile="$1"
  local allowlist="$2"
  local expected="$3"
  local out rc=0
  out=$(lake env lean "$axfile" 2>&1) || rc=$?
  printf '%s\n' "$out"
  if [ "$rc" -ne 0 ]; then
    echo "FAIL: axiom check did not elaborate (lake env lean rc=$rc) -- a '#print axioms' target may have been renamed or removed" >&2
    return 1
  fi
  # Lean may wrap a long dependency list across physical lines. Normalize each complete theorem
  # report before counting and parsing so a longer qualified theorem name cannot break the gate.
  local reports
  reports=$(printf '%s\n' "$out" | awk '
    / depends on axioms: / {
      report = $0
      while (report !~ /\]$/ && (getline continuation) > 0) {
        report = report " " continuation
      }
      print report
      next
    }
    / does not depend on any axioms$/ { print }
  ')
  local got
  got=$(printf '%s\n' "$reports" | grep -cE "^'[^']+' (depends on axioms|does not depend on any axioms)" || true)
  if [ "$expected" -le 0 ] || [ "$got" -ne "$expected" ]; then
    echo "FAIL: axiom check reported on $got of $expected targets -- it did not check every theorem" >&2
    return 1
  fi

  local dependency_reports parsed_reports dependencies axiom
  dependency_reports=$(printf '%s\n' "$reports" | grep -cE "^'[^']+' depends on axioms:" || true)
  parsed_reports=$(printf '%s\n' "$reports" \
    | grep -cE "^'[^']+' depends on axioms: \[[^]]*\]$" || true)
  if [ "$parsed_reports" -ne "$dependency_reports" ]; then
    echo "FAIL: parsed $parsed_reports of $dependency_reports dependency-bearing axiom reports" >&2
    return 1
  fi
  dependencies=$(printf '%s\n' "$reports" \
    | sed -nE "s/^'[^']+' depends on axioms: \[(.*)\]$/\1/p" \
    | tr ',' '\n' \
    | sed -E 's/^[[:space:]]+//; s/[[:space:]]+$//' \
    | grep -v '^$' || true)
  while IFS= read -r axiom; do
    [ -z "$axiom" ] && continue
    if ! grep -Fxq "$axiom" "$allowlist"; then
      echo "FAIL: theorem report names undeclared axiom '$axiom'" >&2
      return 1
    fi
  done <<EOF
$dependencies
EOF
}

# --self-test: deliberately trigger each failure mode and assert the gate FLAGS it (returns
# non-zero). This is the mechanical fence — if the gate ever regresses to fail-open, a mode below
# stops being flagged and this returns non-zero, reddening CI.
run_selftest() {
  echo "== SELF-TEST: the gate must FAIL-CLOSED on every failure mode =="
  SELFTEST_TMP=$(mktemp -d)
  local tmp="$SELFTEST_TMP" fails=0
  mkdir -p "$tmp/src"

  # A: a `sorry` token in a source must be flagged.
  printf 'theorem selftest_a : True := by\n  sorry\n' > "$tmp/src/A.lean"
  if scan_sorry_admit "$tmp/src" >/dev/null 2>&1; then
    echo "  FAIL: a 'sorry' source was not flagged"; fails=$((fails + 1))
  else echo "  ok: 'sorry' flagged"; fi
  rm -f "$tmp/src/A.lean"

  # B: an `admit` token in a source must be flagged.
  printf 'example : True := by admit\n' > "$tmp/src/B.lean"
  if scan_sorry_admit "$tmp/src" >/dev/null 2>&1; then
    echo "  FAIL: an 'admit' source was not flagged"; fails=$((fails + 1))
  else echo "  ok: 'admit' flagged"; fi
  rm -f "$tmp/src/B.lean"

  # C: a missing scan target must be flagged, not silently treated as clean.
  if scan_sorry_admit "$tmp/missing" >/dev/null 2>&1; then
    echo "  FAIL: a missing scan target was treated as clean"; fails=$((fails + 1))
  else echo "  ok: missing target flagged"; fi

  # H: a NEW `native_decide` must be flagged -- it leaves the kernel.
  printf 'example : True := by native_decide\n' > "$tmp/src/H.lean"
  if scan_native_decide 0 "$tmp/src" >/dev/null 2>&1; then
    echo "  FAIL: a new native_decide was not flagged"; fails=$((fails + 1))
  else echo "  ok: new native_decide flagged"; fi
  rm -f "$tmp/src/H.lean"

  # I: an environment census that does NOT elaborate must be flagged, never read as empty.
  printf 'import %s\nrun_cmd do this_is_not_a_command_selftest_xyzzy\n' "$ROOT_MODULE" > "$tmp/census_bad.lean"
  if run_census "$tmp/census_bad.lean" "$tmp/census_bad.txt" >/dev/null 2>&1; then
    echo "  FAIL: a non-elaborating environment census passed"; fails=$((fails + 1))
  else echo "  ok: non-elaborating environment census flagged"; fi

  # I2: a census that ELABORATES but reports nothing must be flagged. Mode I above only drives
  # the non-elaborating path; this drives the empty-output path, so an empty census can never
  # read as "nothing to check" -- the fail-open shape this whole gate exists to prevent.
  printf 'import %s\n' "$ROOT_MODULE" > "$tmp/census_empty.lean"
  if run_census "$tmp/census_empty.lean" "$tmp/census_empty.txt" >/dev/null 2>&1; then
    echo "  FAIL: an empty environment census passed"; fails=$((fails + 1))
  else echo "  ok: empty environment census flagged"; fi

  # K: a theorem in a file OUTSIDE the root import closure must be flagged -- the environment
  # census cannot see unimported modules, so nothing else would check it.
  mkdir -p "$tmp/closure/Orphan"
  printf 'import LambdaSigil\n' > "$tmp/closure/LambdaSigil.lean"
  printf 'theorem selftest_orphan : True := trivial\n' > "$tmp/closure/Orphan/K.lean"
  if (cd "$tmp/closure" && scan_unimported_are_proof_free LambdaSigil .) >/dev/null 2>&1; then
    echo "  FAIL: a theorem in an unimported file was not flagged"; fails=$((fails + 1))
  else echo "  ok: theorem outside the import closure flagged"; fi
  printf 'def main : IO Unit := pure ()\n' > "$tmp/closure/Orphan/K.lean"
  if (cd "$tmp/closure" && scan_unimported_are_proof_free LambdaSigil .) >/dev/null 2>&1; then
    echo "  ok: a proof-free unimported file is allowed"
  else echo "  FAIL: a proof-free unimported file was rejected"; fails=$((fails + 1)); fi

  # J: a census/manifest disagreement must be flagged in BOTH directions.
  printf 'Chk.alpha\nChk.beta\n' > "$tmp/census_two.txt"
  printf 'Chk.alpha\n' > "$tmp/manifest_short.txt"
  printf 'Chk.alpha\nChk.beta\nChk.gamma\n' > "$tmp/manifest_long.txt"
  if compare_census "$tmp/census_two.txt" "$tmp/manifest_short.txt" >/dev/null 2>&1; then
    echo "  FAIL: a theorem absent from the manifest passed"; fails=$((fails + 1))
  else echo "  ok: manifest-escaping theorem flagged"; fi
  if compare_census "$tmp/census_two.txt" "$tmp/manifest_long.txt" >/dev/null 2>&1; then
    echo "  FAIL: a manifest entry absent from the environment passed"; fails=$((fails + 1))
  else echo "  ok: phantom manifest entry flagged"; fi

  # D: deleting one theorem from the committed target inventory must violate the independent pin.
  sed '$d' "$AXIOM_TARGETS" > "$tmp/targets_short.txt"
  if validate_identifier_manifest "$tmp/targets_short.txt" "$PIN_AXIOM_TARGETS" "theorem-target" >/dev/null 2>&1; then
    echo "  FAIL: a shrunken theorem inventory passed its independent pin"; fails=$((fails + 1))
  else echo "  ok: shrunken theorem inventory flagged"; fi

  # E: THE fail-open case -- an axiom check that does NOT elaborate must be flagged (Lean exits
  # non-zero and never prints sorryAx; a grep-only gate would have called this clean).
  printf '#print axioms this_does_not_exist_selftest_xyzzy\n' > "$tmp/ax_bad.lean"
  if check_axioms "$tmp/ax_bad.lean" "$AXIOM_ALLOWLIST" 1 >/dev/null 2>&1; then
    echo "  FAIL: a non-elaborating axiom check passed (fail-open regression!)"; fails=$((fails + 1))
  else echo "  ok: non-elaborating axiom check flagged"; fi

  # F: positive detector proof -- a theorem that genuinely depends on sorryAx (elaborates with a
  # warning, exit 0) must be flagged by the sorryAx check itself, not merely by an elaboration error.
  printf 'theorem selftest_e : True := by sorry\n#print axioms selftest_e\n' > "$tmp/ax_sorry.lean"
  if check_axioms "$tmp/ax_sorry.lean" "$AXIOM_ALLOWLIST" 1 >/dev/null 2>&1; then
    echo "  FAIL: a sorryAx-dependent theorem passed (detector broken!)"; fails=$((fails + 1))
  else echo "  ok: sorryAx dependency flagged"; fi

  # G: a valid custom axiom must fail even though it is not named sorryAx.
  cat > "$tmp/ax_extra.lean" <<'EOF'
axiom selftest_extra : Prop
theorem selftest_extra_uses : Prop := selftest_extra
#print axioms selftest_extra_uses
EOF
  if check_axioms "$tmp/ax_extra.lean" "$AXIOM_ALLOWLIST" 1 >/dev/null 2>&1; then
    echo "  FAIL: an undeclared custom axiom passed"; fails=$((fails + 1))
  else echo "  ok: undeclared custom axiom flagged"; fi

  # L: a planted indirect dependency on a forbidden sanitized symbol must be found through the
  # elaborated declaration graph.  The target's own name is deliberately clean.
  cat > "$tmp/raw_dep_bad.lean" <<'EOF'
import LambdaSigil.RawClaimDependencyAudit
axiom safeMode : True
theorem planted_clean_claim_name : True := safeMode
run_cmd do
  reportRawClaimDependencies (← Lean.getEnv) [`planted_clean_claim_name]
EOF
  if check_raw_claim_dependencies "$tmp/raw_dep_bad.lean" 1 "$RAW_FORBIDDEN_DEPENDENCIES" >/dev/null 2>&1; then
    echo "  FAIL: a transitive safeMode dependency passed the raw-claim audit"; fails=$((fails + 1))
  else echo "  ok: transitive sanitized dependency flagged"; fi

  # M: the retired Public theorem is forbidden by its exact declaration basename.  This planted
  # dependency proves the precise ban remains fail-closed while the production audit above proves
  # that the suffixed V9 corollary is not caught by an over-broad substring.
  cat > "$tmp/raw_legacy_public_bad.lean" <<'EOF'
import LambdaSigil.RawClaimDependencyAudit
namespace LambdaSigil.Combined.Semantic
axiom raw_public_delimited_release_noninterference : True
end LambdaSigil.Combined.Semantic
theorem planted_clean_legacy_public_claim : True :=
  LambdaSigil.Combined.Semantic.raw_public_delimited_release_noninterference
run_cmd do
  reportRawClaimDependencies (← Lean.getEnv) [`planted_clean_legacy_public_claim]
EOF
  if check_raw_claim_dependencies "$tmp/raw_legacy_public_bad.lean" 1 "$RAW_FORBIDDEN_DEPENDENCIES" >/dev/null 2>&1; then
    echo "  FAIL: the exact retired Public theorem passed the raw-claim audit"; fails=$((fails + 1))
  else echo "  ok: exact retired Public theorem dependency flagged"; fi

  # N: test-only oracles/witnesses are not production relational proofs, even when their own
  # theorems are kernel checked. Plant every forbidden test namespace independently so dropping
  # one regex alternative cannot be hidden by another matching alternative.
  local witness_namespace
  for witness_namespace in OccurrenceReference V8OccurrenceProbes PublicRegionProbes ReleaseSynchronizationWitnesses DecodedOccurrenceWitnesses InvocationWitnesses AncestorIntervalWitnesses WireWitnesses PriorityOccurrenceWitnesses IntervalEscapeWitnesses RankedDecodedOccurrenceWitnesses V9SourceOccurrenceChecks OccurrenceActivationWitnesses OccurrenceActivationSourceChecks BoundaryWitnesses DataflowWitnesses PrivateLeafReturnWitnesses; do
    cat > "$tmp/raw_reference_bad.lean" <<EOF
import LambdaSigil.RawClaimDependencyAudit
namespace $witness_namespace
theorem test_only_oracle : True := True.intro
end $witness_namespace
theorem planted_clean_reference_claim : True := $witness_namespace.test_only_oracle
run_cmd do
  reportRawClaimDependencies (← Lean.getEnv) [\`planted_clean_reference_claim]
EOF
    if check_raw_claim_dependencies "$tmp/raw_reference_bad.lean" 1 "$RAW_FORBIDDEN_DEPENDENCIES" >/dev/null 2>&1; then
      echo "  FAIL: test-only $witness_namespace passed the raw-claim audit"; fails=$((fails + 1))
    else echo "  ok: transitive test-only $witness_namespace dependency flagged"; fi
  done

  if [ "$fails" -ne 0 ]; then
    echo "SELF-TEST FAILED: $fails failure mode(s) were not fail-closed"
    return 1
  fi
  echo "SELF-TEST PASS: source, native_decide, census, inventory, elaboration, axiom, and raw-claim dependency failures are closed."
}
