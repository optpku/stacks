module

public import ReasLib.CategoryTheory.Fibered.Stack.Pullback.Pseudofunctor.Action.Underlying

import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for fixed-base pullback on stacks

This leaf exposes the componentwise action, naturality, and vertical-composition laws of pulled
back `2`-cells.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.StackOver.Pullback

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- A component of a pulled-back stack `2`-morphism is the neutral pullback component. -/
@[simp, stacks 04WC "stack-pullback 2-cell component"]
theorem map₂.app
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    (x : CategoricalPullback u X.p) :
    (StackOver.Hom₂.toNatTrans (map₂ (J := J) (K := K) u eta)).app x =
      FiberedCategoryOver.Pullback.mapApp u eta.hom x := sorry

/-- The base component of a pulled-back stack `2`-morphism is the identity. -/
@[simp, stacks 04WC "stack-pullback 2-cell base component"]
theorem map₂.app.fst
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    (x : CategoricalPullback u X.p) :
    ((StackOver.Hom₂.toNatTrans
      (map₂ (J := J) (K := K) u eta)).app x).fst = 𝟙 x.fst := sorry

/-- The total-category component of a pulled-back stack `2`-morphism is the original vertical
component on the second pullback coordinate. -/
@[simp, stacks 04WC "stack-pullback 2-cell total component"]
theorem map₂.app.snd
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    (x : CategoricalPullback u X.p) :
    ((StackOver.Hom₂.toNatTrans
      (map₂ (J := J) (K := K) u eta)).app x).snd =
      (FiberedCategoryOver.toNatTrans eta.hom).app x.snd := sorry

/-- Components of a pulled-back stack `2`-morphism are natural in the categorical-pullback
object. -/
@[stacks 04WC "stack-pullback 2-cell component naturality"]
theorem map₂.naturality
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    {x y : CategoricalPullback u X.p} (f : x ⟶ y) :
    (StackOver.Hom.toFunctor (map (J := J) (K := K) u F)).map f ≫
        (StackOver.Hom₂.toNatTrans
          (map₂ (J := J) (K := K) u eta)).app y =
      (StackOver.Hom₂.toNatTrans
        (map₂ (J := J) (K := K) u eta)).app x ≫
        (StackOver.Hom.toFunctor (map (J := J) (K := K) u G)).map f := sorry

/-- Pullback of stacks preserves identity `2`-morphisms. -/
@[simp, stacks 04WC "stack-pullback 2-cell identity"]
theorem map₂.id
    {X Y : StackOver.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    map₂ (J := J) (K := K) u (𝟙 F) =
      𝟙 (map (J := J) (K := K) u F) := sorry

/-- Pullback of stacks preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 04WC "stack-pullback 2-cell composition"]
theorem map₂.comp
    {X Y : StackOver.{uD, vD, uS, vS} K}
    {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ (J := J) (K := K) u (eta ≫ theta) =
      map₂ (J := J) (K := K) u eta ≫
        map₂ (J := J) (K := K) u theta := sorry

end CategoryTheory.StackOver.Pullback
