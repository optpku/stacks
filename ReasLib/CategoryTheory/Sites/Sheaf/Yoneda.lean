/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Yoneda formulations of the sheaf condition

This leaf packages the coverwise Yoneda condition as a characterization of a
type-valued presheaf being a sheaf.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type v)

/-- A type-valued presheaf is a sheaf precisely when every covering sieve satisfies its Yoneda
sheaf condition. -/
theorem isSheaf_iff_forall_yonedaSheafCondition :
    CategoryTheory.Presheaf.IsSheaf J F ↔
      ∀ ⦃U : C⦄ (S : Sieve U), S ∈ J U →
        CategoryTheory.Presieve.YonedaSheafCondition F S := sorry

end CategoryTheory.Presheaf
