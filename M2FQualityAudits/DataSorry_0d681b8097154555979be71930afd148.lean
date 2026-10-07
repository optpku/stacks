module

import Lean

public import Mathlib.CategoryTheory.CatCommSq
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import stacks_project.Chap59.Lemma_59_103_2_Comparison

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped MorphismOfTopoiIn

noncomputable section

universe u

/-- Lemma 59.103.2 (1): for a morphism `f : X ⟶ Y` in `(Sch/S)_h`, the
big h and big étale direct-image functors form a commutative square. -/
@[stacks 0EW9]
theorem bigHEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Scheme.H.Big.morphismOfTopoi f.left).pushforward
      (Scheme.HComparison.epsilon X.left).pushforward
      (Scheme.HComparison.epsilon Y.left).pushforward
      (Scheme.Etale.Big.morphismOfTopoi f.left).pushforward) := sorry

/-- Lemma 59.103.2 (2): after composing the h-to-étale comparison with the
small-to-big étale morphisms, the resulting direct-image square commutes. -/
@[stacks 0EW9]
theorem hSmallEtaleCommSq {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    Nonempty (CatCommSq
      (Scheme.H.Big.morphismOfTopoi f.left).pushforward
      ((Scheme.HComparison.epsilon X.left).pushforward ⋙
        (Scheme.Etale.SmallToBig.siteMorphismOfTopoi X.left).pushforward)
      ((Scheme.HComparison.epsilon Y.left).pushforward ⋙
        (Scheme.Etale.SmallToBig.siteMorphismOfTopoi Y.left).pushforward)
      (Scheme.Etale.SmallToBig.smallMorphism f.left).pushforward) := sorry

end

end


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
