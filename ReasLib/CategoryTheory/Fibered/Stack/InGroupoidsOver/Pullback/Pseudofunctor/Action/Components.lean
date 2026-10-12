/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Action.Underlying
import Mathlib.Tactic.CrossRefAttribute

/-!
# Component computations for fixed-base pullback on stacks in groupoids

This leaf exposes the componentwise action, naturality, and vertical-composition laws of pulled
back `2`-cells.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.StackOver.Groupoids.Pullback

open CategoryTheory Limits

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)
variable [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u] [u.IsContinuous J K]

/-- A component of a pulled-back stack-in-groupoids `2`-morphism is its neutral groupoid-fibred
component. -/
@[simp, stacks 04WD "groupoid-stack pullback two-cell component"]
theorem map₂.app
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    (map₂ (J := J) (K := K) u eta).hom.hom.toNatTrans.app x =
      (FiberedCategoryOver.Groupoids.Pullback.map₂ u eta.hom).hom.toNatTrans.app x := sorry

/-- The base component of a pulled-back stack-in-groupoids `2`-morphism is the identity. -/
@[simp, stacks 04WD "groupoid-stack pullback base component"]
theorem map₂.app.fst
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    ((map₂ (J := J) (K := K) u eta).hom.hom.toNatTrans.app x).fst =
      𝟙 x.fst := sorry

/-- The total-category component of a pulled-back stack-in-groupoids `2`-morphism is the original
vertical component on the second pullback coordinate. -/
@[simp, stacks 04WD "groupoid-stack pullback total component"]
theorem map₂.app.snd
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) (x : CategoricalPullback u X.p) :
    ((map₂ (J := J) (K := K) u eta).hom.hom.toNatTrans.app x).snd =
      eta.hom.hom.toNatTrans.app x.snd := sorry

/-- Components of a pulled-back stack-in-groupoids `2`-morphism are natural in the categorical-
pullback object. -/
@[stacks 04WD "groupoid-stack pullback component naturality"]
theorem map₂.naturality
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G)
    {x y : CategoricalPullback u X.p} (f : x ⟶ y) :
    (StackOver.Groupoids.Hom.toFunctor (map (J := J) (K := K) u F)).map f ≫
        (map₂ (J := J) (K := K) u eta).hom.hom.toNatTrans.app y =
      (map₂ (J := J) (K := K) u eta).hom.hom.toNatTrans.app x ≫
        (StackOver.Groupoids.Hom.toFunctor (map (J := J) (K := K) u G)).map f := sorry

/-- Pullback of stacks in groupoids preserves identity `2`-morphisms. -/
@[simp, stacks 04WD "groupoid-stack pullback identity two-cell"]
theorem map₂.id
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    map₂ (J := J) (K := K) u (𝟙 F) =
      𝟙 (map (J := J) (K := K) u F) := sorry

/-- Pullback of stacks in groupoids preserves vertical composition of `2`-morphisms. -/
@[simp, stacks 04WD "groupoid-stack pullback two-cell composition"]
theorem map₂.comp
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    map₂ (J := J) (K := K) u (eta ≫ theta) =
      map₂ (J := J) (K := K) u eta ≫
        map₂ (J := J) (K := K) u theta := sorry

end CategoryTheory.StackOver.Groupoids.Pullback
