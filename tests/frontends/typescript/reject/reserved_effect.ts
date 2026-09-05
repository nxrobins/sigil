// expect-fe: FE213
// `Alloc`/`Unsafe`/`FFI` are compiler-reserved effect names with special
// semantics; an author @effects name may not collide with them (F11).
/** @effects Alloc */
function f(x: number): number {
  return x;
}
