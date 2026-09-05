// expect-fe: FE030
// A negative @cap deadline cannot be emitted as a SIGIL parametric-cap literal:
// the SIGIL lexer tokenizes `-1` as Minus + IntLit(1), which the cap-usage
// parser rejects (T198), and an i64::MIN magnitude overflows the lexer's literal
// parse (L001). It is rejected up front with a clean policy code rather than
// emitting text that would only fail the FE500 self-check (a translator-bug code).
/** @cap Net(deadline=-1) */
function f(x: number): number {
  return x;
}
