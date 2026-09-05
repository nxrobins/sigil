// expect-fe: FE302
// The compiler silently accepts a partial record; the translator must enforce
// all-declared-fields-present (H1, the records spine).
interface Point {
  x: number;
  y: number;
}

function make(a: number): Point {
  return { x: a };
}
