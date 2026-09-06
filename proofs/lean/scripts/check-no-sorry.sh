#!/usr/bin/env bash
# CI gate for the λ-SIGIL development: fail if any `sorry`/`admit` appears in the sources, if a
# kernel-external `native_decide` appears, if the pinned theorem inventory drifts, or if any theorem
# depends on an axiom outside the pinned allowlist.
#
# FAIL-CLOSED BY CONSTRUCTION — and fenced against the fail-open bug CLASS.
# The class: a verification gate that infers "pass" from the ABSENCE of a bad-string match, without
# confirming the checker actually RAN and reported on every target. Concretely, the old axiom check
#     if lake env lean AxCheckCI.lean ... | grep -q 'sorryAx'; then FAIL; fi; echo ok
# let its verdict be decided by grep alone: if AxCheckCI.lean stopped ELABORATING (a headline
# theorem was renamed/removed), Lean exits non-zero and never prints `sorryAx`, so grep matched
# nothing and the gate printed "ok"/PASS — silently checking nothing. Here every checker's exit
# status and output-completeness are verified, so that case fails the gate.
#
# The fence has three parts and this file carries all three:
#   1. the gate is fail-closed (the checkers live in scripts/lib/gate.sh, shared with the research
#      overlay's gate so both packages are held to the same fence);
#   2. `--self-test` PROVES the gate red-flags every failure mode — sorry, admit, a new
#      native_decide, a missing scan target, a non-elaborating or empty environment census, a
#      census/manifest disagreement in EITHER direction, target-list shrinkage, a non-elaborating
#      axiom check (the exact bug above), a real sorryAx dependency, and an undeclared axiom;
#   3. CI runs `--self-test` as its own step (.github/workflows/lean.yml), so a future regression
#      back to fail-open cannot land. Mirrors ci.yml's `diag_axes_scoreboard.py --self-test` pattern.
#
# Usage:
#   bash scripts/check-no-sorry.sh              run the gate (from proofs/lean)
#   bash scripts/check-no-sorry.sh --self-test  prove the gate fails closed on every failure mode
set -euo pipefail
cd "$(dirname "$0")/.."

readonly ROOT_MODULE="LambdaSigil"
readonly SOURCE_DIR="LambdaSigil"
readonly AXIOM_TARGETS="axiom-targets.txt"
readonly AXIOM_ALLOWLIST="axiom-allowlist.txt"
readonly PIN_AXIOM_TARGETS=1298
readonly PIN_ALLOWED_AXIOMS=3
# Zero, and confined nowhere: the public development carries no kernel-external proof. The
# seventeen legacy `example` witnesses of the first interaction-net campaign live in the research
# overlay (proofs/lean-research), which pins them there.
readonly PIN_NATIVE_DECIDE=0
readonly NATIVE_DECIDE_DIR=""
# No module filter: this package imports nothing but itself, so every theorem the root's
# environment carries is this development's own.
readonly CENSUS_MODULE_PREFIX=""
readonly PIN_RAW_CLAIMS=2
# The final alternative for the retired Public theorem is anchored to the dependency basename.
# This continues rejecting the exact legacy symbol without accidentally matching the load-bearing
# `raw_public_delimited_release_noninterference_of_v9_verified` corollary.
readonly RAW_FORBIDDEN_DEPENDENCIES='safeMode|observedPayload|RelationalPolicy|RawPublicDelimitedReleasePolicy|[.|]raw_public_delimited_release_noninterference$|OccurrenceReference|V8OccurrenceProbes|PublicRegionProbes|ReleaseSynchronizationWitnesses|DecodedOccurrenceWitnesses|InvocationWitnesses|AncestorIntervalWitnesses|WireWitnesses|PriorityOccurrenceWitnesses|IntervalEscapeWitnesses|RankedDecodedOccurrenceWitnesses|V9SourceOccurrenceChecks|OccurrenceActivationWitnesses|OccurrenceActivationSourceChecks|BoundaryWitnesses|DataflowWitnesses|PrivateLeafReturnWitnesses'

# shellcheck source=lib/gate.sh
source "scripts/lib/gate.sh"
trap cleanup EXIT

# --- main ---
if [ "${1:-}" = "--self-test" ]; then
  run_selftest
  exit 0
fi

echo "== scanning sources for sorry/admit =="
scan_sorry_admit "$SOURCE_DIR/" "$ROOT_MODULE.lean"
echo "ok: no sorry/admit in sources"

echo "== scanning sources for native_decide (kernel-external) =="
scan_native_decide "$PIN_NATIVE_DECIDE" "$SOURCE_DIR/" "$ROOT_MODULE.lean"
echo "ok: no kernel-external native_decide in the development (pinned count $PIN_NATIVE_DECIDE)"

echo "== auditing raw-relational theorem dependency closures =="
write_raw_claim_audit RawClaimAuditCI.lean
check_raw_claim_dependencies RawClaimAuditCI.lean "$PIN_RAW_CLAIMS" "$RAW_FORBIDDEN_DEPENDENCIES"
echo "ok: $PIN_RAW_CLAIMS production raw claims have no sanitized or assumed-policy dependency"

echo "== validating complete theorem and allowed-axiom manifests =="
validate_identifier_manifest "$AXIOM_TARGETS" "$PIN_AXIOM_TARGETS" "theorem-target"
validate_allowlist "$AXIOM_ALLOWLIST"

echo "== checking nothing provable lives outside the root import closure =="
scan_unimported_are_proof_free "$ROOT_MODULE" "$SOURCE_DIR"
echo "ok: every file the census cannot see declares no theorem"

echo "== deriving the theorem census from Lean's elaborated environment =="
write_census_ci CensusCI.lean
CENSUS_LIST=$(mktemp)
run_census CensusCI.lean "$CENSUS_LIST"
compare_census "$CENSUS_LIST" "$AXIOM_TARGETS"
echo "ok: the elaborated environment yields exactly the $PIN_AXIOM_TARGETS manifest theorems"

echo "== checking every theorem depends only on declared standard axioms =="
write_axcheck AxCheckCI.lean "$AXIOM_TARGETS"
check_axioms AxCheckCI.lean "$AXIOM_ALLOWLIST" "$PIN_AXIOM_TARGETS"
echo "ok: all $PIN_AXIOM_TARGETS theorems depend only on the $PIN_ALLOWED_AXIOMS declared axioms"
echo "PASS"
