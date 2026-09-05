// FE1 fixture: an effect-mode policy. @effects becomes an outer-ring SIGIL
// effect row; effect-leakage is enforced by the compiler's E001. `sync` declares
// NetIO, so its call to `fetch` (which requires NetIO) is permitted.
/** @effects NetIO */
function fetch(timeout: number): number {
  return timeout + 1;
}

/** @effects NetIO, FsIO */
function sync(a: number): number {
  return fetch(a) + 1;
}
