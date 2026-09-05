import LambdaSigil.OccurrenceWire

/-!
Bytecode-side transport for shared declaration fixtures. Each requested file receives exactly
one verdict line from the real v9 decoder; this driver neither runs a verifier nor authorizes a
host. Accepted lines also expose retained version/counts and complete profile bytes, so matching
booleans cannot conceal a lost declaration. The Rust fixture generator owns the answer keys.
-/

private def hexDigit (character : Char) : Option Nat :=
  if '0' ≤ character && character ≤ '9' then some (character.toNat - '0'.toNat)
  else if 'a' ≤ character && character ≤ 'f' then some (character.toNat - 'a'.toNat + 10)
  else none

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

private def hex (bytes : ByteArray) : String :=
  let digits := "0123456789abcdef".toList.toArray
  String.ofList (bytes.data.toList.flatMap fun byte =>
    [digits[byte.toNat / 16]!, digits[byte.toNat % 16]!])

def main (paths : List String) : IO UInt32 := do
  if paths.isEmpty then
    IO.eprintln "v9 declaration parity requires a nonempty fixture list"
    return 1
  for path in paths do
    let text ← IO.FS.readFile path
    let some bytes := parseHex text
      | throw (IO.userError s!"invalid fixture hex: {path}")
    match LambdaSigil.Combined.V9.decode bytes with
    | none => IO.println s!"CSIRV9|{path}|1|0|0|0|0|0|0|-"
    | some program =>
        let profile := if program.hostProfileBytes.isEmpty then "-" else hex program.hostProfileBytes
        IO.println s!"CSIRV9|{path}|0|{program.wireVersion}|{program.base.nodes.size}|{program.hostProfileBytes.size}|{program.ffiBindings.size}|{program.actorBindings.size}|{program.roots.size}|{profile}"
  return 0
