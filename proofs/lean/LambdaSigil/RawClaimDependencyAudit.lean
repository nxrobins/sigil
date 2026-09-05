import LambdaSigil.RawClaimSurface

/-!
Environment-level dependency report for the production raw-relational claim surface.

The CI gate asks this module to walk declaration types and values transitively. Reporting the
complete closure lets the gate apply a deliberately small forbidden-name policy without trusting
source-text imports or theorem pretty-printing.
-/

open Lean

def rawClaimDeclarationValue? : ConstantInfo → Option Expr
  | .defnInfo value => some value.value
  | .thmInfo value => some value.value
  | .opaqueInfo value => some value.value
  | _ => none

partial def collectRawClaimDependencies (env : Environment) (pending : List Name)
    (seen : Std.HashSet Name := {}) : Except String (Std.HashSet Name) := do
  match pending with
  | [] => pure seen
  | name :: rest =>
      if seen.contains name then
        collectRawClaimDependencies env rest seen
      else
        let info <- match env.find? name with
          | some info => pure info
          | none => throw s!"missing declaration {name}"
        let direct := info.type.getUsedConstants
        let direct := match rawClaimDeclarationValue? info with
          | some value => direct.foldl (init := value.getUsedConstants)
              fun (accumulated : Array Name) dependency => accumulated.push dependency
          | none => direct
        collectRawClaimDependencies env (direct.toList ++ rest) (seen.insert name)

def reportRawClaimDependencies (env : Environment) (targets : List Name) : IO Unit := do
  if targets.isEmpty then
    throw <| IO.userError "raw claim dependency audit received no targets"
  for target in targets do
    unless env.contains target do
      throw <| IO.userError s!"raw claim dependency audit target is missing: {target}"
    let closure <- match collectRawClaimDependencies env [target] with
      | .ok closure => pure closure
      | .error message => throw <| IO.userError message
    IO.println s!"RAWCLAIM|{target}|{closure.size}"
    for dependency in closure.toArray.qsort (fun left right => left.toString < right.toString) do
      IO.println s!"RAWDEP|{target}|{dependency}"
