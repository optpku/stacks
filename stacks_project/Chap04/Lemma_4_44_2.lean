/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Postcompose
import StacksCheckRecall

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X' Y' X Y : B} {y : T ⟶ Y'} {p : X' ⟶ Y'}
variable {q : X' ⟶ X} {g : Y' ⟶ Y} {f : X ⟶ Y}
variable (sq : Bicategory.PseudoPullbackCone y p) (φ : p ≫ g ≅ q ≫ f)
variable [Bicategory.IsLocallyGroupoid B]
variable [Bicategory.PseudoPullbackCone.IsBilimit
  (⟨X', q, p, φ.symm⟩ : Bicategory.PseudoPullbackCone f g)]

/- Lemma 4.44.2: postcomposition by a `2`-cartesian right square induces an equivalence on
dotted-arrow categories. -/
@[stacks 0H1A]
#check (DottedArrow.postcomposeFunctor.isEquivalence sq φ :
  (DottedArrow.postcomposeFunctor sq φ).IsEquivalence)

end CategoryTheory
