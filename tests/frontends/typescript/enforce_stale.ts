// Enforcement fixture: this translates and compiles clean on its own, but a
// build whose --build-deadline is past 2020 must reject it with T199 (the cap
// would be stale before execution). The translator is untrusted; SIGIL enforces.
/** @cap Net(deadline=2020) */
function fetch(timeout: number): number {
  return timeout;
}
