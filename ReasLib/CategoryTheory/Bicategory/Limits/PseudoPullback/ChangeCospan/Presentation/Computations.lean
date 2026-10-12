/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Presentation.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Pseudofunctor.Basic

/-!
# Computations for the readable/generic change-of-cospan presentation comparison

This leaf identifies the generic pseudocone underlying readable change of cospan and records
the vertex and component formulas for the presentation comparison.
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

/-- The generic pseudocone underlying `changeCospan` is postcomposition by the
corresponding strong transformation of walking-cospan diagrams. This bridge makes
the readable construction an interface to the shape-independent
`PseudoCone.postcompose` owner. -/
@[simp]
theorem changeCospan.toPseudoCone
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).toPseudoCone =
      (PseudoCone.postcompose ψ).obj S.toPseudoCone := sorry
/- Proof strategy: apply pseudocone extensionality. The apex is unchanged; on the three
walking-cospan vertices, unfold `changeCospan` and compare its boundary pasting with vertical
composition of the two strong transformations. -/

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

/- The declarations in this leaf are proposition-valued readouts and introduce no additional
presentation data. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
