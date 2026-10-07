module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Transporting pseudopullback cones along cospan transformations

This module contains the data-level action of a cospan transformation on a readable
pseudopullback cone. It is independent of bilimits and chosen universal lifts.

The boundary pasting is the explicit `iso` field of `PseudoPullbackCone.changeCospan`, with a
dedicated computation theorem in the owner namespace.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Transport a pseudopullback cone along a cospan transformation. Its apex is unchanged,
its projections are postcomposed with the endpoint maps, and its comparison is the canonical
boundary pasting. -/
def changeCospan (S : PseudoPullbackCone f g) (ψ : CospanTransform f g f' g') :
    PseudoPullbackCone f' g' where
  pt := S.pt
  fst := S.fst ≫ ψ.left
  snd := S.snd ≫ ψ.right
  iso :=
    α_ S.fst ψ.left f' ≪≫
      whiskerLeftIso S.fst ψ.leftIso ≪≫
      (α_ S.fst f ψ.base).symm ≪≫
      whiskerRightIso S.iso ψ.base ≪≫
      α_ S.snd g ψ.base ≪≫
      whiskerLeftIso S.snd ψ.rightIso.symm ≪≫
      (α_ S.snd ψ.right g').symm

/-- Changing the cospan leaves the cone apex unchanged. -/
@[simp]
theorem changeCospan.pt (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).pt = S.pt := sorry

/-- The left projection after changing cospan is postcomposition with the left endpoint map. -/
@[simp]
theorem changeCospan.fst (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).fst = S.fst ≫ ψ.left := sorry

/-- The right projection after changing cospan is postcomposition with the right endpoint map. -/
@[simp]
theorem changeCospan.snd (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).snd = S.snd ≫ ψ.right := sorry

/-- The transported comparison isomorphism is the boundary pasting of the original comparison
with the two generating naturality isomorphisms. -/
@[simp]
theorem changeCospan.iso (S : PseudoPullbackCone f g)
    (ψ : CospanTransform f g f' g') :
    (S.changeCospan ψ).iso =
      α_ S.fst ψ.left f' ≪≫
        whiskerLeftIso S.fst ψ.leftIso ≪≫
        (α_ S.fst f ψ.base).symm ≪≫
        whiskerRightIso S.iso ψ.base ≪≫
        α_ S.snd g ψ.base ≪≫
        whiskerLeftIso S.snd ψ.rightIso.symm ≪≫
        (α_ S.snd ψ.right g').symm := sorry

/- Data audit (mathlib 4.32): `changeCospan` reports `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx`. The apex, legs, and pasted comparison are the
explicit data above; `sorryAx` is inherited from the Prop-valued coherence fields of the
walking-cospan pseudofunctors underlying `CospanTransform`, not from a placeholder datum in
this module. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
