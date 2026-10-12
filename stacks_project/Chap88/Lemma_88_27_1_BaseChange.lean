/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import stacks_project.Chap70.Lemma_70_19_1_BaseChange
public import stacks_project.Chap88.«88_27_0_1_Completion»

/-!
# Base change of the completion-functor source and target categories

Slice base change along a morphism of locally Noetherian algebraic spaces
lifts to `Source X T`, and along the induced map of completions to
`Target X T`. Algebraic-space pullbacks use `overPullback` so the fibre
product data are those of sheaf pullbacks rather than chosen pullbacks of
`HasPullbacks (AlgebraicSpace S)`. Formal-space pullbacks use
`Over.pullback` in the functor category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- Base change along `h : X1 ⟶ X` preserves being locally of finite type and an
isomorphism over the complementary open of `T`. -/
theorem sourceBaseChange_mem {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    locallyOfFiniteTypeIsoOverOpenProperty
        (openComplementι X1 (T.preimage (Points.continuous_map h)))
        ((overPullback h).obj Y.obj) :=
  sorry

/-- Base change along `h : X1 ⟶ X` as a functor `Source X T ⥤ Source X1 T1`,
where `T1` is the inverse image of `T` on `X1`. -/
def sourceBaseChange {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) :
    Source X T ⥤ Source X1 (T.preimage (Points.continuous_map h)) :=
  ObjectProperty.lift
    (locallyOfFiniteTypeIsoOverOpenProperty
      (openComplementι X1 (T.preimage (Points.continuous_map h))))
    (LocallyOfFiniteTypeIsoOverOpen.inclusion (openComplementι X T) ⋙ overPullback h)
    (fun Y ↦ sourceBaseChange_mem h T Y)

/-- After inclusion into the slice, `sourceBaseChange` is ordinary slice base
change along `h`. -/
theorem sourceBaseChange_obj {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (Y : Source X T) :
    ((sourceBaseChange h T).obj Y).obj = Over.mk (overPullbackSnd h Y.obj) :=
  sorry

/-- On morphisms, `sourceBaseChange` is the induced map of fibre products. -/
theorem sourceBaseChange_hom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y') :
    ((sourceBaseChange h T).map φ).hom.left = overPullbackMap h φ.hom :=
  sorry

/-- Base change along `map h T` preserves being a locally Noetherian rig-étale
morphism of formal algebraic spaces. -/
theorem targetBaseChange_mem {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T) :
    FormalAlgebraicSpace.isLocallyNoetherianRigEtaleOver
        (completionAlong X1 (T.preimage (Points.continuous_map h)))
        ((Over.pullback (map h T)).obj W.obj) :=
  sorry

/-- Base change along `map h T : X1_/T1 ⟶ X_/T` as a functor
`Target X T ⥤ Target X1 T1`. -/
def targetBaseChange {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) :
    Target X T ⥤ Target X1 (T.preimage (Points.continuous_map h)) :=
  ObjectProperty.lift
    (FormalAlgebraicSpace.isLocallyNoetherianRigEtaleOver
      (completionAlong X1 (T.preimage (Points.continuous_map h))))
    (FormalAlgebraicSpace.LocallyNoetherianRigEtaleOver.inclusion (completionAlong X T) ⋙
      Over.pullback (map h T))
    (fun W ↦ targetBaseChange_mem h T W)

/-- The structure morphism of a `targetBaseChange` object is the second
projection of the functor-category pullback along `map h T`. -/
theorem targetBaseChange_obj {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) (W : Target X T) :
    ((targetBaseChange h T).obj W).obj.hom = pullback.snd W.obj.hom (map h T) :=
  sorry

/-- On morphisms, `targetBaseChange` is `Over.pullback (map h T)`. -/
theorem targetBaseChange_hom {S : Scheme.{u}} {X X1 : AlgebraicSpace S}
    [IsLocallyNoetherian X] [IsLocallyNoetherian X1] (h : X1 ⟶ X)
    (T : Closeds (Points X)) {W W' : Target X T} (ψ : W ⟶ W') :
    ((targetBaseChange h T).map ψ).hom = (Over.pullback (map h T)).map ψ.hom :=
  sorry

end completionAlong

end AlgebraicGeometry.AlgebraicSpace
