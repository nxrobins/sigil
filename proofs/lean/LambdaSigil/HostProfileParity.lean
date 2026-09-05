import LambdaSigil.HostProfileKernel

/-!
Executable bytecode-side parity driver for the shared Rust/Lean host-profile fixtures. File IO
and hexadecimal parsing are test transport only; the verdict comes from the actual kernel.
The linked-native test requires one report per requested file and rejects nonzero driver exits.
-/

private def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

-- The accumulator avoids quadratic repeated array concatenation on long-name fixtures.

private def parseHex (text : String) : Option ByteArray := do
  let text := text.toList.filter (fun character => !character.isWhitespace)
  if text.length % 2 != 0 then none
  let mut bytes := ByteArray.empty
  let mut high : Option Nat := none
  for character in text do
    let value ← hexDigit character
    match high with
    | none => high := some value
    | some upper =>
        bytes := bytes.push (UInt8.ofNat (upper * 16 + value))
        high := none
  if high.isSome then none else some bytes

def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "host profile parity requires a nonempty fixture list"
    return 1
  for path in paths do
    let text ← IO.FS.readFile path
    let some bytes := parseHex text
      | throw (IO.userError s!"invalid fixture hex: {path}")
    let verdict := LambdaSigil.Combined.HostProfile.validateBytes bytes
    IO.println s!"HOSTPROFILE|{path}|{verdict}"
  return 0
