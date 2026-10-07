module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.RepresentedBy
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable presheaves

This file records the Yoneda-isomorphism characterization of representability.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Definition 26.15.1: a presheaf is representable exactly when it is
isomorphic to the Yoneda presheaf of an object. -/
@[stacks 01JG]
theorem isRepresentable_iff_exists_yoneda_obj_iso (F : Cᵒᵖ ⥤ Type v) :
    F.IsRepresentable ↔ ∃ X : C, IsIsomorphic (yoneda.obj X) F := sorry

end CategoryTheory
