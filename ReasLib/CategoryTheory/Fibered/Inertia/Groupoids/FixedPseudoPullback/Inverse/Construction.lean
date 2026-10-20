/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Groupoids.FixedPseudoPullback.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Inverse.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed groupoid-fibred relative-inertia comparison inverse construction

The explicit inverse of the fixed relative-inertia comparison and its
fibred-category owner-level interface.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.Groupoids.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedPseudoPullbackOwner

variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}

/-- The explicit inverse to the relative-inertia comparison in the fixed bicategory of
categories fibred in groupoids. -/
@[stacks 034H "fixed groupoid-fibred inverse diagonal comparison"]
noncomputable def diagonalComparison.inverse (F : X ⟶ Y) :
    CategoryTheory.TwoFibreProduct.apex
        (relativeDiagonal F) (relativeDiagonal F) ⟶
      relativeInertia F :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse
      (FiberedCategoryOver.Groupoids.toBasedFunctor F))

/-- Forgetting the groupoid-fibration owner from the explicit comparison inverse recovers the
neutral based inverse. -/
@[simp]
theorem diagonalComparison.inverse.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (diagonalComparison.inverse F) =
      BasedFunctor.RelativeInertia.diagonalComparison.inverse
        (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- The total functor underlying the groupoid-fibred comparison inverse is the explicit neutral
based comparison inverse. -/
@[simp]
theorem diagonalComparison.inverse.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (diagonalComparison.inverse F) =
      (BasedFunctor.RelativeInertia.diagonalComparison.inverse
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).toFunctor := sorry

/-- The based inverse diagonal comparison preserves strongly cartesian morphisms, giving the
canonical bridge to the ambient fibred-category hom owner. -/
theorem diagonalComparison.inverse.preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse
      (FiberedCategoryOver.Groupoids.toBasedFunctor F)).PreservesStronglyCartesian := sorry

end FixedPseudoPullbackOwner

end FiberedCategoryOver.Groupoids.RelativeInertia

end CategoryTheory
