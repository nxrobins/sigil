// expect-fe: FE021
// A valid TS identifier that collides with a SIGIL keyword must be rejected,
// never emitted verbatim (would misparse as P026) — threat T8.
function f(region: number): number {
  return region;
}
