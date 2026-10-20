/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Transport.PseudoCone.Postcompose.Basic

/-!
# Constructing the readable/generic change-of-cospan presentation comparison

Changing a readable pseudopullback cone and postcomposing its generic walking-cospan
pseudocone give two presentations with the same apex. Their central legs are related by
associators and the naturality isomorphism of the cospan transformation.

This leaf owns the concrete vertexwise comparison and its bundled invertible modification.
The modification naturality theorem remains here because it is a direct proof input to the
bundled construction; readout formulas are kept in `Presentation.Computations`.
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

/-- The vertexwise isomorphism from the readable changed-cospan presentation to generic
pseudocone postcomposition.

The endpoint components are identities. The central component is the canonical pasting
through the left naturality isomorphism of `ψ`. -/
def changeCospan.presentation.iso
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    ∀ j : LocallyDiscrete Limits.WalkingCospan,
      (S.changeCospan ψ).toPseudoCone.π.app j ≅
        (PseudoCone.postcomposeObj ψ S.toPseudoCone).π.app j
  | ⟨Limits.WalkingCospan.one⟩ =>
      α_ S.fst ψ.left f' ≪≫
        whiskerLeftIso S.fst ψ.leftIso ≪≫
          (α_ S.fst f ψ.base).symm
  | ⟨Limits.WalkingCospan.left⟩ =>
      Iso.refl (S.fst ≫ ψ.left)
  | ⟨Limits.WalkingCospan.right⟩ =>
      Iso.refl (S.snd ≫ ψ.right)

/-- The central readable/generic presentation comparison for change of cospan.

This semantic projection keeps downstream code independent of the concrete name of the central
walking-cospan vertex. -/
abbrev changeCospan.presentation.baseIso
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.fst ≫ ψ.left) ≫ f' ≅ (S.fst ≫ f) ≫ ψ.base :=
  changeCospan.presentation.iso S ψ
    (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- The vertexwise readable/generic presentation comparisons satisfy modification
naturality. This is the proof input used to bundle `changeCospan.presentation.iso` as an
invertible modification. -/
theorem changeCospan.presentation.iso.naturality
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    ∀ {a b : LocallyDiscrete Limits.WalkingCospan} (h : a ⟶ b),
      (Pseudofunctor.const
          (LocallyDiscrete Limits.WalkingCospan) S.pt).map h ◁
            (changeCospan.presentation.iso S ψ b).hom ≫
          ((PseudoCone.postcomposeObj ψ S.toPseudoCone).π.naturality h).hom =
        ((S.changeCospan ψ).toPseudoCone.π.naturality h).hom ≫
          (changeCospan.presentation.iso S ψ a).hom ▷
            (cospan f' g').map h := sorry

/-- The readable changed-cospan transformation is isomorphic to generic pseudocone
postcomposition.

This invertible modification, rather than an equality of pseudocones, is the canonical
presentation bridge available in an arbitrary bicategory. -/
def changeCospan.presentation.modification.iso
    (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).toPseudoCone.π ≅
      (PseudoCone.postcomposeObj ψ S.toPseudoCone).π :=
  Pseudofunctor.StrongTrans.isoMk
    (changeCospan.presentation.iso S ψ)
    (changeCospan.presentation.iso.naturality S ψ)

/- Data and axiom audit (mathlib 4.32):

`changeCospan.presentation.iso` explicitly selects identity endpoint components and the
associator/naturality pasting at the central vertex.
`changeCospan.presentation.modification.iso` retains those components through
`Pseudofunctor.StrongTrans.isoMk`; its deferred content is only modification naturality
and inherited coherence. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
