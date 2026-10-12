/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Lean

public import stacks_project.Chap61.Lemma_61_12_13_Identity
public import stacks_project.Chap61.Lemma_61_12_16_Pullback

/-!
# Small pro-étale morphisms of topoi on a chosen site

This leaf owns the morphism of small pro-étale topoi induced by a carrier
morphism `f : T ⟶ S` in a chosen big pro-étale presentation, together with
its comparison identities against `i_f`, `π_S`, and `f_big`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u v w

namespace AlgebraicGeometry.ChosenBigProetaleSite
namespace SmallToBig

variable {X : ChosenBigProetaleSite.{u, v}} {S T : X.carrier}

/-- The morphism of topoi induced by small pro-étale base change along `f`. -/
def smallMorphism (f : T ⟶ S)
    [HasWeakSheafify (smallTopology X T) (Type w)] :
    MorphismOfTopoiIn.{max u v, max u v, v, v, w}
      (smallTopology X S) (smallTopology X T) :=
  IsMorphismOfSites.toMorphismOfTopoiIn (smallPullback f)

/-- The direct image along `f_small` evaluates a sheaf on the base-changed
small pro-étale object. -/
theorem smallMorphism_pushforward_obj_obj (f : T ⟶ S)
    [HasWeakSheafify (smallTopology X T) (Type w)]
    (F : Sheaf (smallTopology X T) (Type w)) (U : smallSite X S) :
    ((smallMorphism f).pushforward.obj F).1.obj (op U) =
      F.1.obj (op ((smallPullback f).obj U)) := sorry

/-- The small-to-big relocalization morphism factors through the big
pro-étale morphism. -/
theorem morphism_eq_comp_big (f : T ⟶ S)
    [HasSheafify (smallTopology X T) (Type w)] :
    morphismOfTopoi f =
      MorphismOfTopoiIn.comp (Big.morphismOfTopoi f) (morphismOfTopoi (𝟙 T)) :=
  sorry

/-- The square comparing small and big pro-étale morphisms of topoi
commutes. -/
theorem smallMorphism_comp_site (f : T ⟶ S)
    [HasWeakSheafify (smallTopology X T) (Type w)]
    [HasWeakSheafify (bigTopology X S) (Type w)]
    [HasWeakSheafify (bigTopology X T) (Type w)] :
    MorphismOfTopoiIn.comp (smallMorphism f) (siteMorphismOfTopoi X T) =
      MorphismOfTopoiIn.comp (siteMorphismOfTopoi X S) (Big.morphismOfTopoi f) :=
  sorry

/-- The small pro-étale morphism has the expanded big-site factorization. -/
theorem smallMorphism_eq_comp_big (f : T ⟶ S)
    [HasSheafify (smallTopology X T) (Type w)]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    smallMorphism.{u, v, w} f =
      (MorphismOfTopoiIn.comp
        (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, v, w} X S)
          (Big.morphismOfTopoi.{u, v, w} f))
        (morphismOfTopoi.{u, v, w} (𝟙 T)) :
        MorphismOfTopoiIn.{max u v, max u v, v, v, w}
          (smallTopology X S) (smallTopology X T)) := sorry

/-- The small pro-étale morphism is the composite of the small-to-big site
morphism with relocalization. -/
theorem smallMorphism_eq_comp (f : T ⟶ S)
    [HasSheafify (smallTopology X T) (Type w)]
    [HasWeakSheafify (bigTopology X S) (Type w)] :
    smallMorphism.{u, v, w} f =
      (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, v, w} X S)
        (morphismOfTopoi.{u, v, w} f) :
        MorphismOfTopoiIn.{max u v, max u v, v, v, w}
          (smallTopology X S) (smallTopology X T)) := sorry

end SmallToBig
end AlgebraicGeometry.ChosenBigProetaleSite


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
