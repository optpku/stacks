/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Presentation.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Basic

/-!
# Computations for the readable/generic change-of-cospan presentation comparison

This leaf compares the generic pseudocone underlying readable change of cospan with
postcomposition and records the vertex and component formulas for the presentation comparison.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

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

/-- The canonical invertible modification comparing readable change of cospan with
generic postcomposition at their common apex. The central component is the explicit
associator/naturality pasting of `changeCospan.presentation.modification.iso`; the
pseudocones need not be equal in an arbitrary bicategory. -/
abbrev changeCospan.toPseudoCone
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).toPseudoCone.π ≅
      ((PseudoCone.postcompose ψ).obj S.toPseudoCone).π :=
  changeCospan.presentation.modification.iso S ψ

/-- At the left vertex, the readable/generic presentation comparison is the identity
isomorphism. -/
@[simp]
theorem changeCospan.presentation.iso.left
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    changeCospan.presentation.iso S ψ
        (LocallyDiscrete.mk Limits.WalkingCospan.left) =
      Iso.refl (S.fst ≫ ψ.left) := sorry

/-- At the right vertex, the readable/generic presentation comparison is the identity
isomorphism. -/
@[simp]
theorem changeCospan.presentation.iso.right
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    changeCospan.presentation.iso S ψ
        (LocallyDiscrete.mk Limits.WalkingCospan.right) =
      Iso.refl (S.snd ≫ ψ.right) := sorry

/-- The central readable/generic presentation comparison is the canonical boundary pasting
through `ψ.leftIso`. -/
@[simp]
theorem changeCospan.presentation.baseIso_eq
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    changeCospan.presentation.baseIso S ψ =
      α_ S.fst ψ.left f' ≪≫
        whiskerLeftIso S.fst ψ.leftIso ≪≫
          (α_ S.fst f ψ.base).symm := sorry

/-- The forward component of the bundled presentation isomorphism is the corresponding
vertexwise comparison. -/
@[simp]
theorem changeCospan.presentation.modification.iso.hom_app
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g')
    (j : LocallyDiscrete Limits.WalkingCospan) :
    (changeCospan.presentation.modification.iso S ψ).hom.as.app j =
      (changeCospan.presentation.iso S ψ j).hom := sorry

/-- The inverse component of the bundled presentation isomorphism is the inverse
vertexwise comparison. -/
@[simp]
theorem changeCospan.presentation.modification.iso.inv_app
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g')
    (j : LocallyDiscrete Limits.WalkingCospan) :
    (changeCospan.presentation.modification.iso S ψ).inv.as.app j =
      (changeCospan.presentation.iso S ψ j).inv := sorry

/- The comparison aliases the explicit presentation data; the remaining declarations are
proposition-valued readouts. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
