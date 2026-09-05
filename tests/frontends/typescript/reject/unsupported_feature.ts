// expect-fe: FE320
// TS features outside the FE2 subset are fail-closed (H20); an optional field
// (`?`) is one such feature.
interface Config {
  name?: number;
}

function f(c: Config): number {
  return 0;
}
