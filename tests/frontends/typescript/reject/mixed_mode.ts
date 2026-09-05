// expect-fe: FE201
// A file is cap-mode XOR effect-mode (F1): caps need the inner ring, effects the
// outer ring, and cross-ring calls are R004-forbidden. Mixing is deferred.
/** @cap Net(deadline=2030) */
function a(x: number): number {
  return x;
}

/** @effects NetIO */
function b(x: number): number {
  return x;
}
