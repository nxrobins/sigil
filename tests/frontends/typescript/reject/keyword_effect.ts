// expect-fe: FE021
// An effect name that collides with a SIGIL keyword must be rejected, never
// emitted verbatim (reuses the FE0 identifier-hygiene guard; threat T8).
/** @effects region */
function f(x: number): number {
  return x;
}
