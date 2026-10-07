module

public import Mathlib.CategoryTheory.Sites.Subcanonical
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe u v

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
  (U : C) (F : Sheaf J (Type v))

/-
Definition 7.12.3: if J is a subcanonical Grothendieck topology on C, then
J.yoneda : C ⥤ Sheaf J (Type v) is the Yoneda embedding h, it is fully faithful,
and C is thereby a full subcategory of sheaves. Sheaves of the form J.yoneda.obj U
(source h_U, sometimes written underline U) are the representable sheaves.
-/
@[stacks 00WR] #check (J.yoneda.obj U : Sheaf J (Type v))

#check J.yoneda
#check J.yonedaFullyFaithful

/- Following source note, not part of Definition 7.12.3:
Mor(J.yoneda.obj U, F) ≃ F.obj.obj (op U). -/
#check (J.yonedaEquiv : (J.yoneda.obj U ⟶ F) ≃ F.obj.obj (op U))
