// expect-fe: FE010
// A misspelled policy tag must fail closed (threat T1), never be silently
// dropped into a more-permissive contract.
/** @capp Net(deadline=2030) */
function fetch(timeout: number): number {
  return timeout;
}
