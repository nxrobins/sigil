import LambdaSigil.V9OccurrenceDataflow
import LambdaSigil.RankedDecodedOccurrence

/-!
# Exact host-result seed regression witnesses

These fail-closed executable checks exercise the new candidate, not production acceptance,
kernel proofs of fixture acceptance, or raw noninterference. The positive private result travels
through the actual semantic adjacency before controlling an actual decoded branch. Mutants
retain the same source program. General binding and leastness proofs live in the security file.
-/

namespace LambdaSigil.Combined.V9.OccurrenceDataflow.DataflowWitnesses

private def node (op : Op) (id : UInt32) (origin : UInt32 := 0) (actual : UInt32 := 0)
    (required : UInt32 := 0) (ceiling : UInt32 := 0) (aux : UInt32 := 0)
    (flags : UInt8 := 0) (label : Label := .pub) : Node :=
  ⟨op, label, .pub, flags, origin, actual, required, ceiling, aux, id⟩

private def source : Combined.Program :=
  ⟨#[node .semFunction 1 1 1 3 2 0 1,
    node .semValue 2 1 1, node .semValue 3 1 2,
    node .semBlock 4 1 1,
    node .semInstruction 5 1 1 1 3 15 1,
    node .semOperand 6 5 0 3 0 0 3,
    node .semOperand 7 5 1 4 0 0 3,
    node .semOperand 8 5 2 0x6b636974 0 0 3,
    node .semInstruction 9 1 1 2 1 0,
    node .semOperand 10 9 0 1,
    node .semInstruction 11 1 1 0 3 3,
    node .semOperand 12 11 0 2,
    node .semOperand 13 11 1 2 0 0 1,
    node .semOperand 14 11 2 3 0 0 1,
    node .semBlock 15 1 2, node .semInstruction 16 1 2 0 1 4,
    node .semOperand 17 16 0 3 0 0 1,
    node .semBlock 18 1 3, node .semInstruction 19 1 3 0 0 28]⟩

private def word (bytes : ByteArray) (value : UInt32) : ByteArray :=
  (List.range 4).foldl (fun bytes shift =>
    bytes.push (UInt8.ofNat (value.toNat / 2 ^ (8 * shift) % 256))) bytes

private def name (bytes : ByteArray) (value : String) : ByteArray :=
  word bytes (UInt32.ofNat value.utf8ByteSize) ++ value.toUTF8

private def profileBytes : ByteArray := Id.run do
  let mut bytes := word HostProfile.magic 1
  bytes := name bytes "provider"
  bytes := word (word bytes 1) 0
  bytes := word (word bytes 0) 1
  bytes := name (name bytes "ffi") "tick"
  bytes := bytes.push 0
  bytes := word bytes 0
  bytes := word bytes 1
  bytes := bytes ++ ByteArray.mk #[0, 2]
  return word bytes 0

private def profile : HostProfile.Profile :=
  ⟨"provider", 1, #[], #[⟨"ffi", "tick", .pub, #[], #[⟨.i32, .secret⟩], #[]⟩]⟩

private def binding (declared : Bool) : FfiBinding :=
  ⟨5, if declared then 1 else 0, 3, 0, 1, "tick", #[], #[.i32]⟩

private def program (declared : Bool := true) : Program :=
  let bytes := if declared then profileBytes else ByteArray.empty
  let rootId := UInt32.ofNat (source.nodes.size + 3 + (bytes.size + 19) / 20)
  ⟨9, source, bytes, if declared then some profile else none, #[binding declared], #[],
    #[⟨rootId, 1, 0, 0, "run", false, 2, .pub, .pub⟩]⟩

private def labelSummary (declared : Bool) : Option (Label × Label × Label × UInt32) := do
  let analysis ← analyze? (program declared)
  let seed ← analysis.hostSeeds[0]?
  some (labelAt analysis.labels 2, labelAt analysis.labels 3, labelAt analysis.labels 5, seed.cell)

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError s!"v9 host seed regression: {message}")

#eval require (labelSummary true == some (.secret, .secret, .pub, 2))
  "private host result must seed actual value cell and propagate to copy, not instruction cell"

#eval require (labelSummary false == some (.internal, .internal, .pub, 2))
  "absent-profile result must remain Internal"

private def occurrenceSummary : Option (Label × Label × Label × Bool) := do
  let analysis ← analyze? program
  let localAnalysis ← RankedDecodedOccurrence.analyze? (semanticProgram program analysis)
  some (localAnalysis.selectors.getD 2 .pub,
    OccurrenceTransfer.localOccurrenceAt localAnalysis.frontiers 0,
    OccurrenceTransfer.localOccurrenceAt localAnalysis.frontiers 3,
    localAnalysis.regions.conservativeFallback)

#eval require (occurrenceSummary == some (.secret, .pub, .secret, false))
  "private host result must control decoded branch while one-time host call stays Public"

#eval require ((analyze? { program with ffiBindings := #[] }).isNone &&
  (analyze? { program with ffiBindings := #[{ binding true with results := #[.i64] }] }).isNone &&
  (analyze? { program with ffiBindings := #[{ binding true with owner := 9 }] }).isNone)
  "missing, wrong ABI, and wrong owner bindings must refuse"

/- The production self-host fixture has 380,766 records. Scanning a larger array here makes a
   recursive `nodes.toList` collector reproduce its native stack overflow during the ordinary Lean
   build, while the production Array fold remains bounded by heap-backed accumulator storage. -/
private def stackBoundedCollectionCanary : Bool := Id.run do
  let legacy := program false
  let some analysis := analyze? legacy | return false
  let filler := node .semOperand 1
  let large := { legacy with
    base := { legacy.base with nodes := Array.replicate 400_000 filler } }
  let some seeds := collectHostSeeds? large analysis.contracts analysis.semanticIndex
    | return false
  return seeds.isEmpty

#eval require stackBoundedCollectionCanary
  "400,000-record host-seed collection must remain iterative and stack bounded"

/- State labels retain their historical global-offset join across function IDs. The large filler
   tail makes a recursive right fold overflow native stacks, while the accumulator fold remains
   bounded and still selects the maximum matching label. -/
private def stackBoundedStateLabelCanary : Bool :=
  let filler := node .semOperand 1 (label := .secretCT)
  let internalContract := node .semLabelContract 1 1 7 0 0 3 1 .internal
  let secretContract := node .semLabelContract 2 2 7 0 0 3 1 .secret
  let records := internalContract :: secretContract ::
    (Array.replicate 400_000 filler).toList
  (semanticDeclaredStateLabelAtList 7 records).eqb .secret

#eval require stackBoundedStateLabelCanary
  "400,002-record global state-label join must remain iterative and preserve cross-function lub"

private def omittedSeedMutant : Bool := Id.run do
  let some analysis := analyze? program | return false
  let labels := saturate program analysis.semanticIndex
    (semanticSeedLabelsWithIndex source analysis.semanticIndex)
  return (labelAt labels 2).eqb .pub && (labelAt labels 3).eqb .pub &&
    !hostSeedsFlowB analysis.hostSeeds labels

#eval require omittedSeedMutant "omitted host seed mutant must fail the independent result check"

private def parseHex (text : String) : Option ByteArray := do
  let digits := text.toList.filter (fun char => !char.isWhitespace)
  if digits.length % 2 != 0 then none
  let mut bytes := ByteArray.empty
  let mut high : Option Nat := none
  for char in digits do
    let value ← if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
      else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10) else none
    match high with
    | none => high := some value
    | some first =>
        bytes := bytes.push (UInt8.ofNat (first * 16 + value))
        high := none
  if high.isSome then none else some bytes

private def sourceCases : Array (String × String) := #[
  ("declared", include_str ".." / "fixtures" / "csir-v9" / "accept-declared-ffi.hex"),
  ("legacy", include_str ".." / "fixtures" / "csir-v9" / "accept-legacy-unknown-ffi.hex")]

/- Exact bytes generated from the committed compiler fixtures also traverse the new seed path.
    This is executable source-to-wire evidence, not a kernel proof of the fixture's acceptance. -/
#eval show IO Unit from do
  for (name, hex) in sourceCases do
    let some bytes := parseHex hex | throw (IO.userError s!"bad source host fixture hex: {name}")
    let some program := decode bytes | throw (IO.userError s!"source host fixture decode failed: {name}")
    let some analysis := analyze? program | throw (IO.userError s!"source host seed analysis failed: {name}")
    require (analysis.hostSeeds.size == 1 && program.ffiBindings.size == 1)
      s!"{name}: expected one actual host result"
    for seed in analysis.hostSeeds do
      let some owner := program.base.nodes[seed.owner.toNat - 1]?
        | throw (IO.userError s!"missing actual source owner: {name}")
      let some value := indexedSemanticValueNode? analysis.semanticIndex owner.origin owner.required
        | throw (IO.userError s!"missing actual source result: {name}")
      require (value.nodeId == seed.cell && seed.owner != seed.cell &&
        owner.origin == seed.functionId && owner.required == seed.valueId &&
        seed.label.flowsTo (labelAt analysis.labels seed.cell))
        s!"{name}: exact source result cell and saturated host label"

end LambdaSigil.Combined.V9.OccurrenceDataflow.DataflowWitnesses
