import LambdaSigil.OccurrenceWire

/-!
AIR-to-CSIR transfer certificates, profile `APC-1`.

The Rust validator independently enumerates the required transfers from AIR and checks local
definition/use renaming against emitted instructions. This kernel checks each non-identity
transfer against an actual phi operand in the exact v9 program. It does not trust a supplied
graph, label, or verdict. Completeness of the Rust obligation extraction remains a premise.
-/

namespace LambdaSigil.Combined.Projection

structure Transfer where
  functionId : UInt32
  source : UInt32
  target : UInt32
  instruction : UInt32
  operand : UInt32
  deriving Repr, BEq, DecidableEq

def transferOK (program : Combined.Program) (transfer : Transfer) : Bool :=
  match program.nodes[transfer.instruction.toNat - 1]?,
      program.nodes[transfer.operand.toNat - 1]? with
  | some instruction, some operand =>
      transfer.functionId != 0 && transfer.source != 0 && transfer.target != 0 &&
      transfer.instruction != 0 && transfer.operand != 0 &&
      instruction.op == .semInstruction && instruction.aux == 2 &&
      instruction.origin == transfer.functionId && instruction.required == transfer.target &&
      instruction.nodeId == transfer.instruction &&
      operand.op == .semOperand && operand.flags == 0 &&
      operand.origin == transfer.instruction && operand.required == transfer.source &&
      operand.nodeId == transfer.operand &&
      operand.actual.toNat < instruction.ceiling.toNat &&
      transfer.operand.toNat == transfer.instruction.toNat + 1 + operand.actual.toNat
  | _, _ => false

def check (program : Combined.Program) (transfers : Array Transfer) : Bool :=
  transfers.all (transferOK program)

-- Fixed-width, versioned framing; bounds are checked before allocation or iteration.
def decodeTransfers (bytes : ByteArray) : Option (Array Transfer) := do
  if bytes.size < 8 || bytes.size > 64 * 1024 * 1024 then none
  if (← readU32? bytes 0) != 1 then none
  let count := (← readU32? bytes 4).toNat
  if count > 1000000 || bytes.size != 8 + count * 20 then none
  let mut result := #[]
  for i in [0:count] do
    let offset := 8 + i * 20
    result := result.push ⟨← readU32? bytes offset, ← readU32? bytes (offset + 4),
      ← readU32? bytes (offset + 8), ← readU32? bytes (offset + 12),
      ← readU32? bytes (offset + 16)⟩
  return result

def validateBytes (bytes obligations : ByteArray) : UInt64 :=
  match V9.decode bytes, decodeTransfers obligations with
  | some program, some transfers => if check program.base transfers then 0 else 2
  | _, _ => 1

@[export sigil_csir_validate_projection]
def exportedValidate (bytes obligations : ByteArray) : UInt64 := validateBytes bytes obligations

end LambdaSigil.Combined.Projection
