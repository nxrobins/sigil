// expect-fe: FE305
// An unknown/extra field in a record construction is rejected (H1).
interface Point {
  x: number;
  y: number;
}

function make(a: number): Point {
  return { x: a, y: a, z: a };
}
