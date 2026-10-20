/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian automorphism groups in groupoids

This module turns a commutativity hypothesis on the endomorphisms of one
object of a groupoid into the canonical multiplicative `CommGroup` structure
on `End X`.  The group structure is mathlib's `End.group`; only its
commutativity is supplied here.
-/

@[expose] public section

universe u v

namespace CategoryTheory

namespace End

variable {C : Type u} [Category.{v} C]

/-- The multiplicative endomorphism monoid is commutative when categorical
composition at the object is commutative. -/
theorem mul_comm_of_comp_comm [IsGroupoid C] (X : C)
    (h_comm : ∀ f g : X ⟶ X, f ≫ g = g ≫ f) (f g : End X) :
    f * g = g * f := sorry

/-- The canonical commutative-group structure on `End X` in a groupoid whose
endomorphisms at `X` commute under categorical composition. -/
noncomputable def commGroupOfCompComm [IsGroupoid C] (X : C)
    (h_comm : ∀ f g : X ⟶ X, f ≫ g = g ≫ f) :
    CommGroup (End X) :=
  { @End.group C (Groupoid.ofIsGroupoid) X with
    mul_comm := fun f g ↦ mul_comm_of_comp_comm X h_comm f g }

end End

end CategoryTheory
