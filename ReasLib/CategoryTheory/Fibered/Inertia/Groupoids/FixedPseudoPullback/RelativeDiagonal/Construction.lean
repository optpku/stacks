/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.RelativeDiagonal.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fixed groupoid-fibred relative diagonal construction

The relative diagonal into the fixed self two-fibre-product owner, together
with its underlying based and total functors.
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

/-- The relative diagonal as a morphism in the fixed groupoid-fibration bicategory. -/
@[stacks 034H "fixed groupoid-fibred relative diagonal"]
def relativeDiagonal (F : X ⟶ Y) :
    X ⟶ CategoryTheory.TwoFibreProduct.apex F F :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.relativeDiagonal (toBasedFunctor F))

/-- Forgetting the groupoid-fibration owner from the relative diagonal recovers the neutral
based relative diagonal. -/
@[simp]
theorem relativeDiagonal.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (relativeDiagonal F) =
      BasedFunctor.relativeDiagonal (FiberedCategoryOver.Groupoids.toBasedFunctor F) := sorry

/-- The total functor underlying the groupoid-fibred relative diagonal is the neutral based
relative diagonal functor. -/
@[simp]
theorem relativeDiagonal.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Groupoids.toFunctor (relativeDiagonal F) =
      (BasedFunctor.relativeDiagonal
        (FiberedCategoryOver.Groupoids.toBasedFunctor F)).toFunctor := sorry

/-- The based relative diagonal preserves strongly cartesian morphisms, so it can be reused by
the ambient fibred-category API without rebuilding the automatic groupoid-target argument. -/
theorem relativeDiagonal.preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedFunctor.relativeDiagonal
      (FiberedCategoryOver.Groupoids.toBasedFunctor F)).PreservesStronglyCartesian := sorry

end FixedPseudoPullbackOwner

end FiberedCategoryOver.Groupoids.RelativeInertia

end CategoryTheory
