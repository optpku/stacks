module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-!
# Exactness in abelian functor categories

This file exposes the pointwise exactness criterion for short complexes in an abelian functor
category.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ShortComplex

variable {K : Type u₁} [Category.{v₁} K]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]

/-- A short complex in an abelian functor category is exact if and only if each of its
evaluations is exact. -/
@[stacks 018Z "pointwise exactness in an abelian functor category"]
theorem exact_iff_forall_app (S : ShortComplex (K ⥤ A)) :
    S.Exact ↔ ∀ k : K, (S.map ((evaluation K A).obj k)).Exact := sorry

end CategoryTheory.ShortComplex
