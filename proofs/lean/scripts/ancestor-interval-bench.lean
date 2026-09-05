import LambdaSigil.AncestorIntervals

/-!
Standalone structural scaling probe. Run from proofs/lean:
  lake env lean --run scripts/ancestor-interval-bench.lean
  lake env lean --run scripts/ancestor-interval-bench.lean 1000000

This does not measure the linked production verifier or qualify the release overhead target.
It deliberately measures both deep chains and wide stars without invoking the slow oracle.
-/

open LambdaSigil.Combined.OccurrenceRegions LambdaSigil.Combined.AncestorIntervals

def benchmarkForest (size : Nat) (wide : Bool) : EscapeIndex :=
  { parent := (List.range size).map (fun node =>
      if wide then size - 1 else if node + 1 < size then node + 1 else node) |>.toArray
    successRank := Array.replicate size (some 0) }

def measureCase (size : Nat) (wide : Bool) : IO Unit := do
  let forest := benchmarkForest size wide
  let before ← IO.monoNanosNow
  let intervals ← match construct? forest (if size == 0 then [] else [size - 1]) with
    | some index => pure index
    | none => throw (IO.userError s!"construction refused: size={size}, wide={wide}")
  let after ← IO.monoNanosNow
  let queryStart ← IO.monoNanosNow
  let count := (List.range size).foldl (fun count node =>
    if LambdaSigil.Combined.AncestorIntervals.ancestorB forest intervals (size - 1) node then
      count + 1 else count) 0
  if count != size then throw (IO.userError s!"root query mismatch: {count} != {size}")
  let queryEnd ← IO.monoNanosNow
  IO.println s!"shape={if wide then "star" else "chain"} nodes={size} construct_ns={after - before} query_ns={queryEnd - queryStart} queries={count} table_entries={intervals.enter.size + intervals.leave.size + intervals.order.size}"

def main (args : List String) : IO Unit := do
  let sizes := if args.isEmpty then [1000, 8000, 64000] else args.map String.toNat!
  for size in sizes do
    measureCase size false
    measureCase size true
