// expect-fe: FE304
// An object literal whose expected record type is not statically inferable is
// rejected — SIGIL has no anonymous/structural record literal (H13).
function f(a: number): number {
  let o = { x: a };
  return a;
}
