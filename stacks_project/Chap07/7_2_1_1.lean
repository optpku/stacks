/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.RepresentablePresheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite

universe v u

variable {C : Type u} [Category.{v} C] (U : C) (F : Cᵒᵖ ⥤ Type v)

/- 7.2.1.1: for a presheaf of sets F on C and an object U, morphisms
h_U ⟶ F in PSh(C) are identified with sections F(U). This is the Yoneda
lemma: Mor_PSh(C)(h_U, F) = F(U) is the equivalence
CategoryTheory.RepresentablePresheaf.homEquiv : (yoneda.obj U ⟶ F) ≃ F.obj (op U), sending s to
s.app (op U) (𝟙 U). -/
@[stacks 090F] #check (CategoryTheory.RepresentablePresheaf.homEquiv :
  (yoneda.obj U ⟶ F) ≃ F.obj (op U))

#check (CategoryTheory.yonedaEquiv_apply :
  ∀ s : yoneda.obj U ⟶ F, yonedaEquiv s = s.app (op U) (𝟙 U))
