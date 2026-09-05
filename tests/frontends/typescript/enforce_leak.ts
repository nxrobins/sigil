// Enforcement fixture: `handler` calls `fetch` (which requires NetIO) but does
// NOT declare NetIO → the compiler rejects with E001 (effect leakage). The
// translator emits faithfully; SIGIL proves the contract (the FE1 analog of the
// FE0 T199 stale-cap demo).
/** @effects NetIO */
function fetch(timeout: number): number {
  return timeout;
}

function handler(a: number): number {
  return fetch(a);
}
