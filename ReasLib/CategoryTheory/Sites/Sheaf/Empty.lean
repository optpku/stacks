/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Preserves

/-!
# The empty-presieve sheaf condition

For a type-valued presheaf, being a sheaf for the empty presieve is exactly
the terminality of the corresponding section type.
-/

@[expose] public section

open Opposite CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {U : C}

/-- The empty-presieve sheaf condition is equivalent to the existence of a terminal structure on
the section type. -/
theorem isSheafFor_empty_iff_nonempty_isTerminal (P : Cᵒᵖ ⥤ Type w) :
    (⊥ : Presieve U).IsSheafFor P ↔ Nonempty (IsTerminal (P.obj (op U))) := sorry

/-- A presheaf with a unique section over `U` is a sheaf for the empty presieve on `U`. -/
theorem isSheafFor_empty_of_uniqueSections (P : Cᵒᵖ ⥤ Type w)
    [Unique (P.obj (op U))] :
    (⊥ : Presieve U).IsSheafFor P := sorry

end CategoryTheory.Presieve
