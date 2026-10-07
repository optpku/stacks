module

import Lean

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X S : RingedSpace.{u}}

/-- The object property of having Tor-amplitude in `[a, b]` after restriction from
`𝒪_X` to the inverse-image sheaf `f⁻¹𝒪_S`. -/
noncomputable def torAmplitudeInOver (f : X ⟶ S) (a b : ℤ) :
    ObjectProperty (ModuleDerived X) :=
  (RingedSpace.torAmplitudeIn a b).inverseImage (relativeRestriction f)

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` over `S` when its restriction to
`f⁻¹𝒪_S` has that Tor-amplitude. -/
abbrev HasTorAmplitudeInOver (f : X ⟶ S) (E : ModuleDerived X) (a b : ℤ) : Prop :=
  torAmplitudeInOver f a b E

/-- Relative Tor-amplitude is the ordinary Tor-amplitude of the derived restriction to
`f⁻¹𝒪_S`. -/
theorem hasTorAmplitudeInOver_iff (f : X ⟶ S) (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      RingedSpace.HasTorAmplitudeIn ((relativeRestriction f).obj E) a b := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived


namespace M2FDataSorryAudit

open Lean Meta Elab Command

private def containsNonPropSorry (value : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  forEachExpr value fun expr => do
    unless ← found.get do
      let (head, args) := expr.getAppFnArgs
      if head == ``sorryAx && args.size >= 1 then
        unless ← isProp args[0]! do
          found.set true
  found.get

run_cmd do
  let env ← getEnv
  -- `env.constants` also contains imported declarations.  Current-module
  -- declarations are the ones without a `const2ModIdx` entry; restricting the
  -- scan to them is important for remote compilation because `mkModuleData`
  -- materializes and traverses the entire imported environment.  That made a
  -- tiny audit scratch file hit Leanfra's cancellation deadline on large repos.
  for (name, info) in env.constants do
    if (Environment.getModuleIdxFor? env name).isNone then
      if let some value := info.value? true then
        let (hasNonPropSorry, _) ← liftCoreM <| (containsNonPropSorry value).run
        if hasNonPropSorry then
          logInfo m!"M2F_NON_PROP_DATA_SORRY|{privateToUserName name}"

end M2FDataSorryAudit
