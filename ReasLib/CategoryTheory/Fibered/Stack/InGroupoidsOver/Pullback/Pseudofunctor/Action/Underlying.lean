/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Pullback.Pseudofunctor.Action.Construction

/-!
# Underlying action computations for fixed-base pullback on stacks in groupoids

This leaf relates the bundled stack action to its groupoid-fibred, based, and total-category
representatives.
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

/-- The object action of stack-in-groupoids pullback is the canonical bundled pullback. -/
@[simp, stacks 04WD "groupoid pullback pseudofunctor object"]
theorem pseudofunctor.obj (T : StackOver.Groupoids.{uD, vD, uS, vS} K) :
    (pseudofunctor J K u).obj T =
      StackOver.Groupoids.pullback (J := J) (K := K) u T := rfl

/-- The `1`-cell action of stack-in-groupoids pullback is `map`. -/
@[simp, stacks 04WD "groupoid pullback pseudofunctor morphism"]
theorem pseudofunctor.map
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (pseudofunctor J K u).map F = map (J := J) (K := K) u F := rfl

/-- The `2`-cell action of stack-in-groupoids pullback is `map₂`. -/
@[simp, stacks 04WD "groupoid pullback pseudofunctor 2-morphism"]
theorem pseudofunctor.map₂
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor J K u).map₂ eta = map₂ (J := J) (K := K) u eta := rfl

/-- Forgetting the stack condition from a pulled-back `1`-morphism gives neutral pullback of the
underlying groupoid-fibred morphism. -/
@[simp, stacks 04WD "groupoid pullback morphism underlying map"]
theorem map.hom
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    (map (J := J) (K := K) u F).hom =
      FiberedCategoryOver.Groupoids.Pullback.map u F.hom := rfl

/-- The based functor of a pulled-back stack-in-groupoids morphism is the neutral based pullback
map. -/
@[simp, stacks 04WD "groupoid pullback morphism based computation"]
theorem map.toBasedFunctor
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    StackOver.Groupoids.Hom.toBasedFunctor (map (J := J) (K := K) u F) =
      FiberedCategoryOver.Groupoids.toBasedFunctor
        (FiberedCategoryOver.Groupoids.Pullback.map u F.hom) := rfl

/-- The total functor of a pulled-back stack-in-groupoids morphism is the neutral total pullback
functor. -/
@[simp, stacks 04WD "groupoid pullback morphism total computation"]
theorem map.toFunctor
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K} (F : X ⟶ Y) :
    StackOver.Groupoids.Hom.toFunctor (map (J := J) (K := K) u F) =
      FiberedCategoryOver.Groupoids.toFunctor
        (FiberedCategoryOver.Groupoids.Pullback.map u F.hom) := rfl

/-- Forgetting the stack condition from a pulled-back `2`-morphism gives neutral pullback of the
underlying groupoid-fibred `2`-morphism. -/
@[simp, stacks 04WD "groupoid pullback 2-morphism underlying map"]
theorem map₂.hom
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ (J := J) (K := K) u eta).hom =
      FiberedCategoryOver.Groupoids.Pullback.map₂ u eta.hom := rfl

/-- The based natural transformation of a pulled-back stack-in-groupoids `2`-morphism is the
neutral based pullback transformation. -/
@[simp, stacks 04WD "groupoid pullback 2-morphism based computation"]
theorem map₂.toBasedNatTrans
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ (J := J) (K := K) u eta).hom.hom =
      (FiberedCategoryOver.Groupoids.Pullback.map₂ u eta.hom).hom := rfl

/-- The total natural transformation of a pulled-back stack-in-groupoids `2`-morphism is the
neutral total pullback transformation. -/
@[simp, stacks 04WD "groupoid pullback 2-morphism total computation"]
theorem map₂.toNatTrans
    {X Y : StackOver.Groupoids.{uD, vD, uS, vS} K}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ (J := J) (K := K) u eta).hom.hom.toNatTrans =
      (FiberedCategoryOver.Groupoids.Pullback.map₂ u eta.hom).hom.toNatTrans := rfl

end CategoryTheory.StackOver.Groupoids.Pullback
