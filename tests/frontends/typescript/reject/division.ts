// expect-fe: FE031
// `/` is excluded so div-by-zero is structurally impossible (threat T16).
function half(a: number): number {
  return a / 2;
}
