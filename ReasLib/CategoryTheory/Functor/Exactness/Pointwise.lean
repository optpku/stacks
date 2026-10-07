module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise Exactness of Functor-Category Operations

This leaf packages pointwise criteria for exactness of functors valued in a
functor category, together with exactness of precomposition.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.FunctorCategory

variable {B : Type u₁} [Category.{v₁} B]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

/-- A functor into a functor category is left exact exactly when all of its evaluations are left
exact. -/
@[stacks 0192 "pointwise criterion for left exact functors"]
theorem leftExactFunctor_iff_evaluation (F : B ⥤ (D ⥤ A)) :
    leftExactFunctor B (D ⥤ A) F ↔
      ∀ d : D, leftExactFunctor B A (F ⋙ (evaluation D A).obj d) := sorry

/-- A functor into a functor category is right exact exactly when all of its evaluations are
right exact. -/
@[stacks 0192 "pointwise criterion for right exact functors"]
theorem rightExactFunctor_iff_evaluation (F : B ⥤ (D ⥤ A)) :
    rightExactFunctor B (D ⥤ A) F ↔
      ∀ d : D, rightExactFunctor B A (F ⋙ (evaluation D A).obj d) := sorry

/-- A functor into a functor category is exact exactly when all of its evaluations are exact. -/
@[stacks 0192 "pointwise criterion for exact functors"]
theorem exactFunctor_iff_evaluation (F : B ⥤ (D ⥤ A)) :
    exactFunctor B (D ⥤ A) F ↔
      ∀ d : D, exactFunctor B A (F ⋙ (evaluation D A).obj d) := sorry

end CategoryTheory.FunctorCategory

namespace CategoryTheory.Functor

/-- Precomposition along a functor is exact on functor categories. -/
@[stacks 0192 "exactness of precomposition"]
theorem whiskeringLeft_exact
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {A : Type u₃} [Category.{v₃} A] (G : D ⥤ E) :
    exactFunctor (E ⥤ A) (D ⥤ A) ((Functor.whiskeringLeft D E A).obj G) := sorry

end CategoryTheory.Functor
