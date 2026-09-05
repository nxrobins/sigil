// FE0 fixture: a network-capability policy. The @cap annotation becomes an
// inner-ring SIGIL capability contract; the deadline is enforced by T199 under
// `--build-deadline`.
/** @cap Net(deadline=2030) */
function fetch(timeout: number): number {
  return timeout + 1;
}

function compute(a: number, b: number): number {
  return a * b - 2;
}
