import LambdaSigil.CombinedKernel
import Init.Data.Range.Lemmas

/-!
# The kernel-cheap twin of the wire decoder

`Combined.decode` reads its bytes by index, which is what the compiled verifier wants. Under the
kernel an indexed read on a byte literal walks the underlying list, so a `decide +kernel` over a
fixture costs the byte offset per read and grows quadratically in the wire size: the probe
modules' fixture theorems peaked at 7--15 GB in one lean process (measured 2026-09-05). This
module defines `decodeList`, the same decoder consuming the byte list sequentially (every read a
constructor match), and proves `decode_eq_decodeList`, so a fixture theorem about `decode`
rewrites to one about `decodeList` and is decided cheaply. The production decoder is unchanged
and stays the only decoder the compiled verifier runs.
-/

namespace LambdaSigil.Combined.DecoderStream

/-- One byte off the front of the stream, with the unread remainder. -/
def takeU8 : List UInt8 → Option (UInt8 × List UInt8)
  | [] => none
  | byte :: rest => some (byte, rest)

/-- One little-endian 32-bit word off the front of the stream, with the unread remainder. -/
def takeU32 (stream : List UInt8) : Option (UInt32 × List UInt8) := do
  let (a, stream) ← takeU8 stream
  let (b, stream) ← takeU8 stream
  let (c, stream) ← takeU8 stream
  let (d, stream) ← takeU8 stream
  return (a.toUInt32 ||| (b.toUInt32 <<< 8) ||| (c.toUInt32 <<< 16) ||| (d.toUInt32 <<< 24),
    stream)

/-- `Combined.decodeNode?` over the front of the stream, with the unread remainder. -/
def decodeNode? (stream : List UInt8) : Option (Node × List UInt8) := do
  let (opByte, stream) ← takeU8 stream
  let op ← decodeOp? opByte
  let (labelAByte, stream) ← takeU8 stream
  let labelA ← decodeLabel? labelAByte
  let (labelBByte, stream) ← takeU8 stream
  let labelB ← decodeLabel? labelBByte
  let (flags, stream) ← takeU8 stream
  let (origin, stream) ← takeU32 stream
  let (actual, stream) ← takeU32 stream
  let (required, stream) ← takeU32 stream
  let (ceiling, stream) ← takeU32 stream
  let (aux, stream) ← takeU32 stream
  let (nodeId, stream) ← takeU32 stream
  let (reserved, stream) ← takeU32 stream
  if reserved != 0 then none else
    some ({ op, labelA, labelB, flags, origin, actual, required, ceiling, aux, nodeId }, stream)

/-- `Combined.decodeNodes` over the stream, structural on the nodes still to read; `index` is
    the position of the next node. -/
def decodeNodes (stream : List UInt8) : Nat → Nat → Array Node → Option (Array Node)
  | 0, _, nodes => some nodes
  | remaining + 1, index, nodes => do
    let (node, rest) ← decodeNode? stream
    if node.nodeId != UInt32.ofNat (index + 1) then none
    decodeNodes rest remaining (index + 1) (nodes.push node)

/-- `Combined.magicOK` over the stream. -/
def magicOK (stream : List UInt8) : Bool :=
  stream.length ≥ 4 &&
    (stream[0]? == some 0x43) &&
    (stream[1]? == some 0x53) &&
    (stream[2]? == some 0x49) &&
    (stream[3]? == some 0x52)

/-- `Combined.decode` over the byte list. -/
def decodeList (stream : List UInt8) : Option Program := do
  if stream.length > maxWireBytes || stream.length < headerBytes || !magicOK stream then none
  else
  let (version, rest) ← takeU32 (stream.drop 4)
  if version != wireVersion then none else
  let (count32, rest) ← takeU32 rest
  let count := count32.toNat
  if count > maxNodes then none else
  if stream.length != headerBytes + count * nodeBytes then none else
  let nodes ← decodeNodes rest count 0 #[]
  return ⟨nodes⟩

private theorem readU8?_eq (bytes : ByteArray) (offset : Nat) :
    readU8? bytes offset = bytes.data.toList[offset]? := by
  unfold readU8?
  split
  · rename_i h
    rw [List.getElem?_eq_getElem (by simpa using h)]
    rfl
  · rename_i h
    rw [List.getElem?_eq_none (by simpa using h)]

private theorem takeU8_drop (stream : List UInt8) (offset : Nat) :
    takeU8 (stream.drop offset) = stream[offset]?.map (fun byte => (byte, stream.drop (offset + 1))) := by
  by_cases h : offset < stream.length
  · rw [List.drop_eq_getElem_cons h, List.getElem?_eq_getElem h]
    rfl
  · rw [List.drop_eq_nil_of_le (by omega), List.getElem?_eq_none (by omega)]
    rfl

private theorem takeU32_drop (bytes : ByteArray) (offset : Nat) :
    takeU32 (bytes.data.toList.drop offset) =
      (readU32? bytes offset).map (fun word => (word, bytes.data.toList.drop (offset + 4))) := by
  simp only [takeU32, readU32?, bind, pure]
  rw [takeU8_drop, ← readU8?_eq]
  cases readU8? bytes offset with
  | none => rfl
  | some a =>
    dsimp only [Option.bind, Option.map]
    rw [takeU8_drop, ← readU8?_eq]
    cases readU8? bytes (offset + 1) with
    | none => rfl
    | some b =>
      dsimp only [Option.bind, Option.map]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      rw [takeU8_drop, ← readU8?_eq]
      cases readU8? bytes (offset + 2) with
      | none => rfl
      | some c =>
        dsimp only [Option.bind, Option.map]
        simp only [Nat.add_assoc, Nat.reduceAdd]
        rw [takeU8_drop, ← readU8?_eq]
        cases readU8? bytes (offset + 3) with
        | none => rfl
        | some d => dsimp only [Option.bind, Option.map]

private theorem decodeNode?_drop (bytes : ByteArray) (offset : Nat) :
    decodeNode? (bytes.data.toList.drop offset) =
      (Combined.decodeNode? bytes offset).map
        (fun node => (node, bytes.data.toList.drop (offset + 32))) := by
  simp only [decodeNode?, Combined.decodeNode?, bind]
  rw [takeU8_drop, ← readU8?_eq]
  cases readU8? bytes offset with
  | none => rfl
  | some opByte =>
  dsimp only [Option.bind, Option.map]
  cases decodeOp? opByte with
  | none => rfl
  | some op =>
  dsimp only [Option.bind, Option.map]
  rw [takeU8_drop, ← readU8?_eq]
  cases readU8? bytes (offset + 1) with
  | none => rfl
  | some labelAByte =>
  dsimp only [Option.bind, Option.map]
  cases decodeLabel? labelAByte with
  | none => rfl
  | some labelA =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU8_drop, ← readU8?_eq]
  cases readU8? bytes (offset + 2) with
  | none => rfl
  | some labelBByte =>
  dsimp only [Option.bind, Option.map]
  cases decodeLabel? labelBByte with
  | none => rfl
  | some labelB =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU8_drop, ← readU8?_eq]
  cases readU8? bytes (offset + 3) with
  | none => rfl
  | some flags =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 4) with
  | none => rfl
  | some origin =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 8) with
  | none => rfl
  | some actual =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 12) with
  | none => rfl
  | some required =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 16) with
  | none => rfl
  | some ceiling =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 20) with
  | none => rfl
  | some aux =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 24) with
  | none => rfl
  | some nodeId =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  rw [takeU32_drop]
  cases readU32? bytes (offset + 28) with
  | none => rfl
  | some reserved =>
  dsimp only [Option.bind, Option.map]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  split <;> rfl

private theorem decodeNodes_eq_forIn (bytes : ByteArray) (remaining : Nat) :
    ∀ (start : Nat) (nodes : Array Node),
      decodeNodes (bytes.data.toList.drop (headerBytes + start * nodeBytes)) remaining start nodes =
        forIn (List.range' start remaining) nodes (fun i current => do
          let n ← Combined.decodeNode? bytes (headerBytes + i * nodeBytes)
          if n.nodeId != UInt32.ofNat (i + 1) then none
          pure (ForInStep.yield (current.push n))) := by
  induction remaining with
  | zero => intro start nodes; rfl
  | succ remaining ih =>
    intro start nodes
    rw [List.range'_succ, List.forIn_cons]
    simp only [decodeNodes, decodeNode?_drop, bind, pure]
    cases Combined.decodeNode? bytes (headerBytes + start * nodeBytes) with
    | none => rfl
    | some n =>
    dsimp only [Option.bind, Option.map]
    -- `split` rewrites the shared numbering check on both sides at once.
    split
    · rfl
    · have harith :
          headerBytes + start * nodeBytes + 32 = headerBytes + (start + 1) * nodeBytes := by
        simp only [nodeBytes]; omega
      rw [harith, ih]
      rfl

/-- The indexed production decoder and its sequential twin agree on every byte array. -/
theorem decode_eq_decodeList (bytes : ByteArray) :
    Combined.decode bytes = decodeList bytes.data.toList := by
  have hsize : bytes.size = bytes.data.toList.length := rfl
  have hmagic : Combined.magicOK bytes = magicOK bytes.data.toList := by
    simp only [Combined.magicOK, magicOK, readU8?_eq, hsize]
  unfold Combined.decode decodeList
  simp only [hsize, hmagic, bind, pure]
  split
  · rfl
  · rw [takeU32_drop]
    cases readU32? bytes 4 with
    | none => rfl
    | some version =>
    dsimp only [Option.bind, Option.map]
    simp only [Nat.reduceAdd]
    split
    · rfl
    · rw [takeU32_drop]
      cases readU32? bytes 8 with
      | none => rfl
      | some count32 =>
      dsimp only [Option.bind, Option.map]
      simp only [Nat.reduceAdd]
      split
      · rfl
      · split
        · rfl
        · have hnodes := decodeNodes_eq_forIn bytes count32.toNat 0 #[]
          simp only [headerBytes, Nat.zero_mul, Nat.add_zero] at hnodes
          rw [hnodes]
          unfold Combined.decodeNodes
          simp only [bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
            Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
          -- The loop's trailing `return nodes` is a `bind` with `some`, which is the identity.
          rw [show ∀ x : Option (Array Node), x.bind (fun nodes => some nodes) = x from
            fun x => by cases x <;> rfl]
          rfl

end LambdaSigil.Combined.DecoderStream
