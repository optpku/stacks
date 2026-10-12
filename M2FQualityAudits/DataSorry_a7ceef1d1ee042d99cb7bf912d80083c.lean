/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Lean

public import stacks_project.Chap62.Lemma_62_4_5_Specialization

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- Lemma 62.4.5: specialization of `r`-cycles from the generic fibre to the special
fibre of a scheme locally of finite type over a discrete valuation ring commutes with
proper pushforward. -/
@[stacks 0H4M]
theorem specialization_comp_mapHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X Y : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (r : ℕ) :
    (specialization Y r).comp
        (mapHom (genericFiberHom f).left
          ((genericFiber X).hom.relativeDimensionFunction (fun _ ↦ 0))
          ((genericFiber Y).hom.relativeDimensionFunction (fun _ ↦ 0)) r) =
      (mapHom (specialFiberHom f).left
          ((specialFiber X).hom.relativeDimensionFunction (fun _ ↦ 0))
          ((specialFiber Y).hom.relativeDimensionFunction (fun _ ↦ 0)) r).comp
        (specialization X r) := sorry

end AlgebraicGeometry.CycleGroup


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
