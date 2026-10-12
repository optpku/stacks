/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf

@[expose] public section

universe uC vC uA vA

namespace CategoryTheory.Presheaf

/-- A category-valued presheaf is a sheaf precisely when its composite with every
covariant Hom functor is a sheaf of types. -/
theorem isSheaf_iff_forall_isSheaf_coyoneda
    {C : Type uC} [Category.{vC} C] {A : Type uA} [Category.{vA} A]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ A) :
    IsSheaf J F ↔ ∀ object : A, Presieve.IsSheaf J (F ⋙ coyoneda.obj (Opposite.op object)) := sorry

end CategoryTheory.Presheaf
