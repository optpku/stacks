/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.LeftLegDiagonal.Presentation.Central

/-!
# Central computations for left-leg diagonal squares

This leaf records central presentation components and the projection formulas for the final
left-leg diagonal comparison. Together with the endpoint presentation leaf, it gives a complete
three-vertex API without exposing `Pseudofunctor.StrongTrans` or `WalkingCospan` to applications.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

noncomputable section

/-- The forward central comparison of the induced map is the universal central comparison
followed by the constructor readout for the left endpoint. -/
@[simp]
theorem map.baseIso.hom (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (map.baseIso P Q R).hom =
      (PseudoPullbackCone.mapCospan.baseIso Q R (transform P)).hom ≫
        (whiskerRightIso
          (whiskerLeftIso Q.fst
            (eqToIso (CospanTransform.mk_left P.fst P.fst g P.iso P.iso))) f).hom := sorry

/-- The inverse central comparison of the induced map is the reverse canonical pasting. -/
@[simp]
theorem map.baseIso.inv (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [R.IsBilimit] :
    (map.baseIso P Q R).inv =
      (whiskerRightIso
        (whiskerLeftIso Q.fst
          (eqToIso (CospanTransform.mk_left P.fst P.fst g P.iso P.iso))) f).inv ≫
        (PseudoPullbackCone.mapCospan.baseIso Q R (transform P)).inv := sorry

/-- The forward central source presentation is the inverse associator followed by the
first-projection presentation whiskered with `f`. -/
@[simp]
theorem source.baseIso.hom (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (source.baseIso P Q R).hom =
      (α_ (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) R.fst f).inv ≫
        (whiskerRightIso (source.fstIso P Q R) f).hom := sorry

/-- The inverse central source presentation is the reverse canonical pasting. -/
@[simp]
theorem source.baseIso.inv (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (source.baseIso P Q R).inv =
      (whiskerRightIso (source.fstIso P Q R) f).inv ≫
        (α_ (sourceDiagonal P Q ≫ LeftLegDiagonal.map P Q R) R.fst f).hom := sorry

/-- The forward central target presentation is the inverse associator followed by the
first-projection presentation whiskered with `f`. -/
@[simp]
theorem target.baseIso.hom (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (target.baseIso P R).hom =
      (α_ (P.fst ≫ targetDiagonal R) R.fst f).inv ≫
        (whiskerRightIso (target.fstIso P R) f).hom := sorry

/-- The inverse central target presentation is the reverse canonical pasting. -/
@[simp]
theorem target.baseIso.inv (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (target.baseIso P R).inv =
      (whiskerRightIso (target.fstIso P R) f).inv ≫
        (α_ (P.fst ≫ targetDiagonal R) R.fst f).hom := sorry

/-- The central component of the forward source presentation is `source.baseIso`. -/
@[simp]
theorem presentation.left.iso.hom_app_base (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (presentation.left.iso P Q R).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (source.baseIso P Q R).hom := sorry

/-- The central component of the inverse source presentation is the inverse
`source.baseIso`. -/
@[simp]
theorem presentation.left.iso.inv_app_base (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (presentation.left.iso P Q R).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (source.baseIso P Q R).inv := sorry

/-- The central component of the forward target presentation is `target.baseIso`. -/
@[simp]
theorem presentation.right.iso.hom_app_base (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (presentation.right.iso P R).hom.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (target.baseIso P R).hom := sorry

/-- The central component of the inverse target presentation is the inverse
`target.baseIso`. -/
@[simp]
theorem presentation.right.iso.inv_app_base (P : PseudoPullbackCone f g)
    (R : PseudoPullbackCone f f) [R.IsBilimit] :
    (presentation.right.iso P R).inv.as.app
        (LocallyDiscrete.mk Limits.WalkingCospan.one) =
      (target.baseIso P R).inv := sorry

/-- The forward final comparison commutes with the first target projection. -/
@[simp]
theorem iso.hom_fst (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).hom ▷ R.fst =
      (source.fstIso P Q R).hom ≫ (target.fstIso P R).inv := sorry

/-- The inverse final comparison commutes with the first target projection. -/
@[simp]
theorem iso.inv_fst (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).inv ▷ R.fst =
      (target.fstIso P R).hom ≫ (source.fstIso P Q R).inv := sorry

/-- The forward final comparison commutes with the second target projection. -/
@[simp]
theorem iso.hom_snd (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).hom ▷ R.snd =
      (source.sndIso P Q R).hom ≫ (target.sndIso P R).inv := sorry

/-- The inverse final comparison commutes with the second target projection. -/
@[simp]
theorem iso.inv_snd (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).inv ▷ R.snd =
      (target.sndIso P R).hom ≫ (source.sndIso P Q R).inv := sorry

/-- The forward final comparison commutes with the central target leg. -/
@[simp]
theorem iso.hom_base (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).hom ▷ (R.fst ≫ f) =
      (source.baseIso P Q R).hom ≫ (target.baseIso P R).inv := sorry

/-- The inverse final comparison commutes with the central target leg. -/
@[simp]
theorem iso.inv_base (P : PseudoPullbackCone f g)
    (Q : PseudoPullbackCone P.snd P.snd) (R : PseudoPullbackCone f f)
    [Q.IsBilimit] [R.IsBilimit] :
    (iso P Q R).inv ▷ (R.fst ≫ f) =
      (target.baseIso P R).hom ≫ (source.baseIso P Q R).inv := sorry

end

end CategoryTheory.Bicategory.PseudoPullbackCone.LeftLegDiagonal
