// FE2 fixture: interface → record, construction, and field access.
interface Point {
  x: number;
  y: number;
}

function make(a: number, b: number): Point {
  return { x: a, y: b };
}

function sum(p: Point): number {
  return p.x + p.y;
}
