/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Pullback.Pseudofunctor.Action.Construction

/-!
# Underlying action computations for fixed-base pullback in groupoids

This leaf relates the bundled groupoid-fibred action to its neutral based and total-category
representatives.
-/

@[expose] public section

noncomputable section

universe uC uD uS vC vD vS

namespace CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

open CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable (u : C ⥤ D)

/-- The object action of groupoid-fibred pullback is the canonical bundled pullback. -/
@[simp]
theorem pseudofunctor.obj
    (X : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D) :
    (pseudofunctor u).obj X = FiberedCategoryOver.Groupoids.pullback u X := sorry

/-- The `1`-cell action of groupoid-fibred pullback is the named pullback map. -/
@[simp]
theorem pseudofunctor.map
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    (pseudofunctor u).map F = map u F := sorry

/-- The `2`-cell action of groupoid-fibred pullback is the named pullback transformation. -/
@[simp]
theorem pseudofunctor.map₂
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (pseudofunctor u).map₂ eta = map₂ u eta := sorry

/-- Forgetting a pulled-back `1`-morphism to a based functor gives the neutral based pullback
map. -/
@[simp]
theorem map.toBasedFunctor
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (map u F) =
      FiberedCategoryOver.Pullback.basedMap u
        ((FiberedCategoryOver.Groupoids.toFibered D).map F) := sorry

/-- The total functor of a pulled-back groupoid-fibred morphism is the neutral categorical-
pullback comparison. -/
@[simp]
theorem map.toFunctor
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D} (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (map u F) =
      FiberedCategoryOver.Pullback.totalMap u
        ((FiberedCategoryOver.Groupoids.toFibered D).map F) := sorry

/-- Forgetting a pulled-back `2`-morphism gives the neutral based pullback natural
transformation. -/
@[simp]
theorem map₂.toBasedNatTrans
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ u eta).hom =
      FiberedCategoryOver.Pullback.basedMap₂ u
        ((FiberedCategoryOver.Groupoids.toFibered D).map₂ eta) := sorry

/-- The total natural transformation of a pulled-back groupoid-fibred `2`-morphism is the
neutral total pullback transformation. -/
@[simp]
theorem map₂.toNatTrans
    {X Y : FiberedCategoryOver.Groupoids.{uD, vD, uS, vS} D}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (map₂ u eta).hom.toNatTrans =
      FiberedCategoryOver.Pullback.totalMap₂ u
        ((FiberedCategoryOver.Groupoids.toFibered D).map₂ eta) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.Pullback

