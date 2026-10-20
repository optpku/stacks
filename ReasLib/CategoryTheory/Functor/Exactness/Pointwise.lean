module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Pointwise Exactness of Functor-Category Operations

This leaf packages pointwise criteria for exactness of functors valued in a
functor category, together with exactness of precomposition.

Finite limits (resp. colimits) in `D ⥤ A` are computed pointwise only when the target `A` has
them, so the forward directions of the criteria and the exactness of precomposition require
`HasFiniteLimits A` (resp. `HasFiniteColimits A`). The reverse directions are mathlib's
`preservesFiniteLimits_of_evaluation` and `preservesFiniteColimits_of_evaluation`.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.FunctorCategory

variable {B : Type u₁} [Category.{v₁} B]
variable {D : Type u₂} [Category.{v₂} D]
variable {A : Type u₃} [Category.{v₃} A]

/-- If `A` has finite limits, a functor into the functor category `D ⥤ A` is left exact exactly
when all of its evaluations are left exact. -/
theorem leftExactFunctor_iff_evaluation [HasFiniteLimits A] (F : B ⥤ (D ⥤ A)) :
    leftExactFunctor B (D ⥤ A) F ↔
      ∀ d : D, leftExactFunctor B A (F ⋙ (evaluation D A).obj d) := by
  simp only [leftExactFunctor_iff]
  exact ⟨fun _ d => comp_preservesFiniteLimits F ((evaluation D A).obj d),
    preservesFiniteLimits_of_evaluation F⟩

/-- If `A` has finite colimits, a functor into the functor category `D ⥤ A` is right exact
exactly when all of its evaluations are right exact. -/
theorem rightExactFunctor_iff_evaluation [HasFiniteColimits A] (F : B ⥤ (D ⥤ A)) :
    rightExactFunctor B (D ⥤ A) F ↔
      ∀ d : D, rightExactFunctor B A (F ⋙ (evaluation D A).obj d) := by
  simp only [rightExactFunctor_iff]
  exact ⟨fun _ d => comp_preservesFiniteColimits F ((evaluation D A).obj d),
    preservesFiniteColimits_of_evaluation F⟩

/-- If `A` has finite limits and finite colimits, a functor into the functor category `D ⥤ A` is
exact exactly when all of its evaluations are exact. -/
theorem exactFunctor_iff_evaluation [HasFiniteLimits A] [HasFiniteColimits A]
    (F : B ⥤ (D ⥤ A)) :
    exactFunctor B (D ⥤ A) F ↔
      ∀ d : D, exactFunctor B A (F ⋙ (evaluation D A).obj d) := by
  simp only [exactFunctor_iff]
  exact ⟨fun ⟨_, _⟩ d => ⟨comp_preservesFiniteLimits F ((evaluation D A).obj d),
      comp_preservesFiniteColimits F ((evaluation D A).obj d)⟩,
    fun h => ⟨preservesFiniteLimits_of_evaluation F fun d => (h d).1,
      preservesFiniteColimits_of_evaluation F fun d => (h d).2⟩⟩

end CategoryTheory.FunctorCategory

namespace CategoryTheory.Functor

/-- If `A` has finite limits and finite colimits, precomposition along a functor is exact on
functor categories valued in `A`. -/
theorem whiskeringLeft_exact
    {D : Type u₁} [Category.{v₁} D] {E : Type u₂} [Category.{v₂} E]
    {A : Type u₃} [Category.{v₃} A] [HasFiniteLimits A] [HasFiniteColimits A] (G : D ⥤ E) :
    exactFunctor (E ⥤ A) (D ⥤ A) ((Functor.whiskeringLeft D E A).obj G) := by
  rw [exactFunctor_iff]
  exact ⟨inferInstance, inferInstance⟩

end CategoryTheory.Functor
