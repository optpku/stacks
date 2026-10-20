/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.TransformationFunctor.Construction

/-!
# Computations for the changed-cospan transformation functor

This leaf records the object, morphism, and natural-isomorphism component formulas for the
ordinary changed-cospan transformation functor.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- The object action of the readable change-of-cospan functor is the cone
transformation of the corresponding changed cone. -/
@[simp]
theorem changeCospan.transformation.functor.obj
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (changeCospan.transformation.functor S f' g').obj ψ =
      (S.changeCospan ψ).toPseudoCone.π := sorry

/-- The morphism action of the readable change-of-cospan functor is the explicit
conjugated modification. -/
@[simp]
theorem changeCospan.transformation.functor.map
    (S : PseudoPullbackCone f g)
    {ψ φ : CospanTransform f g f' g'} (Γ : ψ ⟶ φ) :
    (changeCospan.transformation.functor S f' g').map Γ =
      changeCospan.modification Γ S := sorry

/-- The forward component of the readable/neutral functor isomorphism is the bundled
presentation comparison. -/
@[simp]
theorem changeCospan.transformation.functor.iso.hom_app
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (changeCospan.transformation.functor.iso S f' g').hom.app ψ =
      (changeCospan.presentation.modification.iso S ψ).hom := sorry

/-- The inverse component of the readable/neutral functor isomorphism is the inverse
bundled presentation comparison. -/
@[simp]
theorem changeCospan.transformation.functor.iso.inv_app
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (changeCospan.transformation.functor.iso S f' g').inv.app ψ =
      (changeCospan.presentation.modification.iso S ψ).inv := sorry

end Bicategory.PseudoPullbackCone

end CategoryTheory
