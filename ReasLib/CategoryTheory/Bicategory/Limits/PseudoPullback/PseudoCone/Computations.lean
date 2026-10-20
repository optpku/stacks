/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Construction

/-!
# Walking-cospan pseudocone computations

This leaf contains the field and generator readouts for the readable-to-generic and
generic-to-readable presentations. It introduces no construction or universal-property data.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The apex of the generic pseudocone associated to a readable pseudopullback square. -/
@[simp]
theorem toPseudoCone.pt (S : PseudoPullbackCone f g) :
    S.toPseudoCone.pt = S.pt := sorry
/- Proof strategy: unfold `toPseudoCone`, `PseudoCone.mk`, and `PseudoCone.pt`; the apex
projection then reduces definitionally. -/

/-- The left vertex component of the generic pseudocone is the left projection of the readable
pseudopullback square. -/
@[simp]
theorem toPseudoCone.π.app_left (S : PseudoPullbackCone f g) :
    S.toPseudoCone.π.app (LocallyDiscrete.mk Limits.WalkingCospan.left) = S.fst := sorry
/- Proof strategy: unfold `toPseudoCone` and the private vertex assembly, then select the left
walking-cospan vertex. -/

/-- The right vertex component of the generic pseudocone is the right projection of the readable
pseudopullback square. -/
@[simp]
theorem toPseudoCone.π.app_right (S : PseudoPullbackCone f g) :
    S.toPseudoCone.π.app (LocallyDiscrete.mk Limits.WalkingCospan.right) = S.snd := sorry
/- Proof strategy: unfold `toPseudoCone` and the private vertex assembly, then select the right
walking-cospan vertex. -/

/-- The central vertex component of the generic pseudocone is the chosen left composite. -/
@[simp]
theorem toPseudoCone.π.app_one (S : PseudoPullbackCone f g) :
    S.toPseudoCone.π.app (LocallyDiscrete.mk Limits.WalkingCospan.one) = S.fst ≫ f := sorry
/- Proof strategy: unfold `toPseudoCone` and the private vertex assembly, then select the central
walking-cospan vertex. -/

/-- Naturality on the left generator is the left unitor of the chosen central composite. -/
@[simp]
theorem toPseudoCone.π.naturality_inl (S : PseudoPullbackCone f g) :
    S.toPseudoCone.π.naturality
      (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl) = λ_ (S.fst ≫ f) := sorry
/- Proof strategy: unfold `toPseudoCone` and the private generator assembly, then select the
left generator. -/

/-- Naturality on the right generator is the left unitor followed by the square comparison. -/
@[simp]
theorem toPseudoCone.π.naturality_inr (S : PseudoPullbackCone f g) :
    S.toPseudoCone.π.naturality
      (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr) = λ_ (S.fst ≫ f) ≪≫ S.iso := sorry
/- Proof strategy: unfold `toPseudoCone` and the private generator assembly, then select the
right generator. The resulting cell has the orientation of `S.iso`. -/

/-- The readable normalization of a generic walking-cospan pseudocone has the same apex. -/
@[simp]
theorem ofPseudoCone.pt (s : PseudoCone (cospan f g)) :
    (ofPseudoCone s).pt = s.pt := sorry
/- Proof strategy: unfold `ofPseudoCone`; the apex is its first explicit constructor datum. -/

/-- The first projection of the readable normalization is the left-vertex cone component. -/
@[simp]
theorem ofPseudoCone.fst (s : PseudoCone (cospan f g)) :
    (ofPseudoCone s).fst =
      s.π.app (LocallyDiscrete.mk Limits.WalkingCospan.left) := sorry
/- Proof strategy: unfold `ofPseudoCone`; the first projection is its second constructor datum. -/

/-- The second projection of the readable normalization is the right-vertex cone component. -/
@[simp]
theorem ofPseudoCone.snd (s : PseudoCone (cospan f g)) :
    (ofPseudoCone s).snd =
      s.π.app (LocallyDiscrete.mk Limits.WalkingCospan.right) := sorry
/- Proof strategy: unfold `ofPseudoCone`; the second projection is its third constructor datum. -/

/-- The comparison of the readable normalization is the composite of the inverse left-generator
naturality isomorphism with the right-generator naturality isomorphism. -/
@[simp]
theorem ofPseudoCone.iso (s : PseudoCone (cospan f g)) :
    (ofPseudoCone s).iso =
      (s.π.naturality
          (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inl)).symm ≪≫
        s.π.naturality
          (Quiver.Hom.toLoc Limits.WalkingCospan.Hom.inr) := sorry
/- Proof strategy: unfold `ofPseudoCone`; the comparison is its fourth explicit constructor datum. -/

/-- Normalizing a square to a generic pseudocone and forgetting it again recovers the original
square. -/
@[simp]
theorem ofPseudoCone.toPseudoCone (S : PseudoPullbackCone f g) :
    ofPseudoCone S.toPseudoCone = S := sorry
/- Proof strategy: apply `PseudoPullbackCone.ext`, use the apex and vertex computation lemmas,
then cancel the inserted left unitors around `S.iso`. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
