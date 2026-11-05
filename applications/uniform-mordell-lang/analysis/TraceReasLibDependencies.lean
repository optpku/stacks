import Lean
import AnnalsChallenge.AnnalsOfMathematics.«2021-194-1-UniformMordellLang»

open Lean Elab Command Meta
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def dependencyOwner (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!.toString
  | none => env.mainModule.toString

def referencedClosure (env : Environment) (roots : Array Name) (skipProofBodies : Bool)
    (cache : IO.Ref (Std.HashMap Name Bool)) : MetaM NameSet := do
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some ci := env.find? name | throwError "Unknown dependency: {name}"
    let mut body := true
    if skipProofBodies then
      let isProof ← match (← cache.get)[name]? with
        | some value => pure value
        | none => do
          let value ← isProp ci.type
          cache.modify fun c => c.insert name value
          pure value
      body := !isProof
    todo := todo ++ ci.type.getUsedConstants
    if body then todo := todo ++ ((ci.value? true).map Expr.getUsedConstants |>.getD #[])
    -- Reached structure/inductive interfaces include their constructor field types.
    if (dependencyOwner env name).startsWith "ReasLib." then
      if let .inductInfo info := ci then todo := todo ++ info.ctors.toArray
  return seen

def dependencyScope (env : Environment) (names : NameSet) : Json := Id.run do
  let mut declarations : Array Json := #[]
  let mut modules : Std.HashSet String := {}
  for name in names do
    let owner := dependencyOwner env name
    if owner.startsWith "ReasLib." then
      modules := modules.insert owner
      declarations := declarations.push <| Json.mkObj [
        ("name", toJson name.toString), ("module", toJson owner)]
  return Json.mkObj [
    ("all_constants", toJson names.size),
    ("reaslib_declaration_count", toJson declarations.size),
    ("reaslib_module_count", toJson modules.size),
    ("reaslib_modules", toJson (modules.toArray.qsort (· < ·))),
    ("reaslib_declarations", toJson declarations)]

elab "#write_declaration_use" : command => do
  let env ← getEnv
  let theoremRoots := #[``UniformMordellLang.theorem_1_1]
  let applicationRoots := #[
    ``AlgebraicGeometry.JacobianChallenge.genus,
    ``AlgebraicGeometry.JacobianChallenge.Jacobian,
    ``AlgebraicGeometry.JacobianChallenge.Jacobian.instGrpObj,
    ``AlgebraicGeometry.JacobianChallenge.Jacobian.ofCurve,
    ``UniformMordellLang.c,
    ``UniformMordellLang.theorem_1_1]
  let cache ← IO.mkRef ({} : Std.HashMap Name Bool)
  let mut scopes : Array (String × Json) := #[]
  for (label, roots, skipProofBodies) in #[
      ("theorem_with_proof_bodies", theoremRoots, false),
      ("theorem_without_proof_bodies", theoremRoots, true),
      ("six_roots_with_proof_bodies", applicationRoots, false),
      ("six_roots_without_proof_bodies", applicationRoots, true)] do
    let names ← liftTermElabM <| referencedClosure env roots skipProofBodies cache
    scopes := scopes.push (label, dependencyScope env names)
    logInfo m!"Computed {label}: {names.size} constants"
  let report := Json.mkObj [
    ("method", toJson "Traverse elaborated declaration types and (optionally) values, including opaque bodies; expand constructors of reached ReasLib inductive/structure types to retain field specifications. Module ownership uses Environment.getModuleIdxFor?. Counts include generated declarations and describe these elaborated terms, not an absolute mathematical minimum or a deletable-file set."),
    ("theorem_roots", toJson (theoremRoots.map Name.toString)),
    ("application_roots", toJson (applicationRoots.map Name.toString)),
    ("loaded_reaslib_modules", toJson ((env.header.moduleNames.filter fun n => n.toString.startsWith "ReasLib.").map Name.toString)),
    ("scopes", Json.mkObj scopes.toList)]
  IO.FS.createDirAll ".work/reuse"
  IO.FS.writeFile ".work/reuse/declaration-use.json" report.pretty

#write_declaration_use
