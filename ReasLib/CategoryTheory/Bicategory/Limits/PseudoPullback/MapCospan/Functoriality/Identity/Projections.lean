/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Hom.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Functoriality.Identity
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Projections
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.StrongTrans

/-!
# Projection formulas for identity coherence of universal pseudopullback maps

The readable identity presentation determines a comparison isomorphism at every
walking-cospan vertex. Its left, right, and central specializations describe the complete
component behavior of the identity apex map.

These component isomorphisms are the canonical conjugating cells in the projection
formulas for `mapCospan.id.iso`. Downstream constructions can therefore use the identity
coherence without unfolding the represented pseudocone comparison.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B}
variable {f : x ⟶ z} {g : y ⟶ z}

/-- The first-projection comparison carried by the complete presentation of the
identity universal map. -/
noncomputable abbrev mapCospan.id.fstIso
    (S : PseudoPullbackCone f g) :
    (𝟙 S.pt) ≫ S.fst ≅
      S.fst ≫ (CospanTransform.id f g).left :=
  Pseudofunctor.StrongTrans.isoApp (mapCospan.id.comparisonIso S)
    (LocallyDiscrete.mk Limits.WalkingCospan.left)

/-- The second-projection comparison carried by the complete presentation of the
identity universal map. -/
noncomputable abbrev mapCospan.id.sndIso
    (S : PseudoPullbackCone f g) :
    (𝟙 S.pt) ≫ S.snd ≅
      S.snd ≫ (CospanTransform.id f g).right :=
  Pseudofunctor.StrongTrans.isoApp (mapCospan.id.comparisonIso S)
    (LocallyDiscrete.mk Limits.WalkingCospan.right)

/-- The central comparison carried by the complete presentation of the identity universal map. -/
noncomputable abbrev mapCospan.id.baseIso
    (S : PseudoPullbackCone f g) :
    (𝟙 S.pt) ≫ (S.fst ≫ f) ≅
      (S.fst ≫ (CospanTransform.id f g).left) ≫ f :=
  Pseudofunctor.StrongTrans.isoApp (mapCospan.id.comparisonIso S)
    (LocallyDiscrete.mk Limits.WalkingCospan.one)

/-- At every walking-cospan vertex, the forward identity coherence is conjugated by
the identity presentation and the universal comparison. -/
@[simp]
theorem mapCospan.id.iso.map_hom_app
    (S : PseudoPullbackCone f g) [S.IsBilimit]
    (j : LocallyDiscrete Limits.WalkingCospan) :
    ((S.toPseudoCone.comparison S.pt).map
        (mapCospan.id.iso S).hom).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapCospan.id.comparisonIso S) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapCospan.comparisonIso S S (CospanTransform.id f g)) j).inv := sorry

/-- At every walking-cospan vertex, the inverse identity coherence is conjugated by
the universal comparison and the inverse identity presentation. -/
@[simp]
theorem mapCospan.id.iso.map_inv_app
    (S : PseudoPullbackCone f g) [S.IsBilimit]
    (j : LocallyDiscrete Limits.WalkingCospan) :
    ((S.toPseudoCone.comparison S.pt).map
        (mapCospan.id.iso S).inv).as.app j =
      (Pseudofunctor.StrongTrans.isoApp
        (mapCospan.comparisonIso S S (CospanTransform.id f g)) j).hom ≫
        (Pseudofunctor.StrongTrans.isoApp
          (mapCospan.id.comparisonIso S) j).inv := sorry

/-- The forward identity coherence commutes with the first projection, conjugated by
the identity and universal first-projection comparisons. -/
@[simp]
theorem mapCospan.id.iso.hom_fst
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).hom ▷ S.fst =
      (mapCospan.id.fstIso S).hom ≫
        (mapCospan.fstIso S S
          (CospanTransform.id f g)).inv := sorry

/-- The inverse identity coherence commutes with the first projection, conjugated by
the universal and inverse identity first-projection comparisons. -/
@[simp]
theorem mapCospan.id.iso.inv_fst
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).inv ▷ S.fst =
      (mapCospan.fstIso S S
          (CospanTransform.id f g)).hom ≫
        (mapCospan.id.fstIso S).inv := sorry

/-- The forward identity coherence commutes with the second projection, conjugated by
the identity and universal second-projection comparisons. -/
@[simp]
theorem mapCospan.id.iso.hom_snd
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).hom ▷ S.snd =
      (mapCospan.id.sndIso S).hom ≫
        (mapCospan.sndIso S S
          (CospanTransform.id f g)).inv := sorry

/-- The inverse identity coherence commutes with the second projection, conjugated by
the universal and inverse identity second-projection comparisons. -/
@[simp]
theorem mapCospan.id.iso.inv_snd
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).inv ▷ S.snd =
      (mapCospan.sndIso S S
          (CospanTransform.id f g)).hom ≫
        (mapCospan.id.sndIso S).inv := sorry

/-- The forward identity coherence commutes with the central leg, conjugated by the identity
and universal central comparisons. -/
@[simp]
theorem mapCospan.id.iso.hom_base
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).hom ▷ (S.fst ≫ f) =
      (mapCospan.id.baseIso S).hom ≫
        (mapCospan.baseIso S S
          (CospanTransform.id f g)).inv := sorry

/-- The inverse identity coherence commutes with the central leg, conjugated by the universal
and inverse identity central comparisons. -/
@[simp]
theorem mapCospan.id.iso.inv_base
    (S : PseudoPullbackCone f g) [S.IsBilimit] :
    (mapCospan.id.iso S).inv ▷ (S.fst ≫ f) =
      (mapCospan.baseIso S S
          (CospanTransform.id f g)).hom ≫
        (mapCospan.id.baseIso S).inv := sorry

/- Data and axiom audit (mathlib 4.32):

The three vertex comparisons transparently evaluate the existing complete identity presentation.
All remaining declarations expose components of the already specified identity coherence. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
