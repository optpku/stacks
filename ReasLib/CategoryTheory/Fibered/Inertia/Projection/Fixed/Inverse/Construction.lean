/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed.Comparison.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.DiagonalComparison.Inverse.Construction
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Closure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fibred relative-inertia comparison inverse construction

This leaf owns the explicit inverse of the fixed fibred-category relative-inertia comparison.
Readout computations live in `Inverse.Computations`.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open BasedCategory BasedFunctor

namespace FiberedCategoryOver.RelativeInertia

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

section FixedOwner

variable {X Y :
  FiberedCategoryOver.{u, v, max w (max u v), v} C}

/-- The explicit inverse of the neutral relative-inertia comparison preserves strongly
cartesian morphisms. -/
theorem diagonalComparison.inverse.preservesStronglyCartesian (F : X ⟶ Y) :
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse
      (FiberedCategoryOver.toBasedFunctor F)).PreservesStronglyCartesian := sorry
/- Proof strategy: the explicit inverse belongs to
`BasedFunctor.RelativeInertia.diagonalComparison.quasiInverse`; apply preservation of strongly cartesian
morphisms by a based equivalence. -/

/-- The explicit inverse to the canonical relative-inertia comparison, retained as a cartesian
morphism in the fixed bicategory of fibred categories. -/
@[stacks 034H "inverse fibred relative-inertia diagonal comparison"]
noncomputable def diagonalComparison.inverse (F : X ⟶ Y) :
    LocallyInduced.TwoFibreProduct.apex
        (RelativeInertia.relativeDiagonal F)
        (RelativeInertia.relativeDiagonal F) ⟶
      relativeInertia F :=
  ofBasedFunctor
    (BasedFunctor.RelativeInertia.diagonalComparison.inverse
      (FiberedCategoryOver.toBasedFunctor F))
    (RelativeInertia.diagonalComparison.inverse.preservesStronglyCartesian F)

/-- Forgetting the fibred-category owner from the explicit comparison inverse recovers the
neutral based inverse. -/
@[simp]
theorem diagonalComparison.inverse.toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toBasedFunctor (RelativeInertia.diagonalComparison.inverse F) =
      BasedFunctor.RelativeInertia.diagonalComparison.inverse
        (FiberedCategoryOver.toBasedFunctor F) := sorry

/-- The total functor underlying the fibred comparison inverse is the explicit neutral based
comparison inverse. -/
@[simp]
theorem diagonalComparison.inverse.toFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.toFunctor (RelativeInertia.diagonalComparison.inverse F) =
      (BasedFunctor.RelativeInertia.diagonalComparison.inverse
        (FiberedCategoryOver.toBasedFunctor F)).toFunctor := sorry

end FixedOwner

end FiberedCategoryOver.RelativeInertia
end CategoryTheory
