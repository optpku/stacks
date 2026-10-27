/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.AtlasRepresentable
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Concrete schemes representing the relative-spectrum diagonal

First use the given base-space diagonal to represent equality of the two base
maps. Pull its stored atlas back and form the actual equalizer of the two local
spectrum lifts. Its invariant closed ideal descends by the native ideal-sheaf
image construction. The resulting subscheme and its explicit lift operation
provide the diagonal pullback witness.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}

/-- The base-space diagonal pullback representing equality of the two actual base arrows. -/
def relativeSpectrumDiagonalBaseOver (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) : Over S :=
  X.representableDiagonal.pullback
    (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))

/-- The actual base coincidence scheme's projection to the common test scheme. -/
def relativeSpectrumDiagonalBaseToTest (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalBaseOver A p q ⟶ T :=
  X.representableDiagonal.snd
    (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))

/-- The first point restricted to the concrete base coincidence scheme. -/
def relativeSpectrumDiagonalBasePoint₁ (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumPair A (relativeSpectrumDiagonalBaseOver A p q) :=
  relativeSpectrumPairMap (relativeSpectrumDiagonalBaseToTest A p q) p

/-- The second point restricted to the concrete base coincidence scheme. -/
def relativeSpectrumDiagonalBasePoint₂ (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumPair A (relativeSpectrumDiagonalBaseOver A p q) :=
  relativeSpectrumPairMap (relativeSpectrumDiagonalBaseToTest A p q) q

set_option backward.isDefEq.respectTransparency false in
/-- The two restricted points have identical base arrows by the stored diagonal pullback. -/
theorem relativeSpectrumDiagonalBasePoints_base (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumPointBase A (relativeSpectrumDiagonalBasePoint₁ A p q) =
      relativeSpectrumPointBase A (relativeSpectrumDiagonalBasePoint₂ A p q) := by
  have hw := X.representableDiagonal.w
    (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))
  have h₁ := congrArg (fun f ↦ f ≫ prod.fst) hw
  have h₂ := congrArg (fun f ↦ f ≫ prod.snd) hw
  simp only [Category.assoc, prod.lift_fst, prod.lift_snd, Category.comp_id] at h₁ h₂
  calc
    relativeSpectrumPointBase A (relativeSpectrumDiagonalBasePoint₁ A p q) =
        NatTrans.vcomp (yoneda.map (relativeSpectrumDiagonalBaseToTest A p q))
          (relativeSpectrumPointBase A p) := yonedaEquiv.symm_apply_apply _
    _ = NatTrans.vcomp (yoneda.map (relativeSpectrumDiagonalBaseToTest A p q))
        (relativeSpectrumPointBase A q) := h₁.symm.trans h₂
    _ = relativeSpectrumPointBase A (relativeSpectrumDiagonalBasePoint₂ A p q) :=
      (yonedaEquiv.symm_apply_apply _).symm

/-- The actual atlas cover of the concrete base coincidence scheme. -/
abbrev relativeSpectrumDiagonalAtlasOver (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) : Over S :=
  relativeSpectrumPointAtlasOver A (relativeSpectrumDiagonalBasePoint₁ A p q)

/-- The atlas-cover projection to the concrete base coincidence scheme. -/
abbrev relativeSpectrumDiagonalAtlasToBase (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalAtlasOver A p q ⟶ relativeSpectrumDiagonalBaseOver A p q :=
  relativeSpectrumPointAtlasToTest A (relativeSpectrumDiagonalBasePoint₁ A p q)

/-- The actual map to the second point's atlas pullback, keeping the same stored-atlas point. -/
def relativeSpectrumDiagonalAtlasToSecond (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalAtlasOver A p q ⟶
      relativeSpectrumPointAtlasOver A (relativeSpectrumDiagonalBasePoint₂ A p q) :=
  yoneda.preimage
    (((atlasHom_presheaf_etale X).rep.isPullback
      (relativeSpectrumPointBase A (relativeSpectrumDiagonalBasePoint₂ A p q))).lift
      (yoneda.map (relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₁ A p q)))
      (yoneda.map (relativeSpectrumDiagonalAtlasToBase A p q)) (by
        rw [← relativeSpectrumDiagonalBasePoints_base A p q]
        exact ((atlasHom_presheaf_etale X).rep.isPullback'
          (relativeSpectrumPointBase A (relativeSpectrumDiagonalBasePoint₁ A p q))).w))

/-- The first concrete local spectrum lift. -/
def relativeSpectrumDiagonalLocalMap₁ (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    (relativeSpectrumDiagonalAtlasOver A p q).left ⟶ (relativeSpectrumDescentAtlas A).left :=
  (relativeSpectrumPointAtlasLift A (relativeSpectrumDiagonalBasePoint₁ A p q)).left

/-- The second concrete local spectrum lift over the same base-atlas chart. -/
def relativeSpectrumDiagonalLocalMap₂ (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    (relativeSpectrumDiagonalAtlasOver A p q).left ⟶ (relativeSpectrumDescentAtlas A).left :=
  (relativeSpectrumDiagonalAtlasToSecond A p q).left ≫
    (relativeSpectrumPointAtlasLift A (relativeSpectrumDiagonalBasePoint₂ A p q)).left

/-- Both local spectrum maps lie over the same point of the stored atlas. -/
theorem relativeSpectrumDiagonalLocalMap₁_over (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalLocalMap₁ A p q ≫
        (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π =
      (relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₁ A p q)).left := by
  exact Scheme.relativeSpectrumPointMap_toBase _
    ⟨(relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₁ A p q)).left,
      relativeSpectrumPointAtlasAlgebraMap A (relativeSpectrumDiagonalBasePoint₁ A p q)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The second local map has the same specified structural composite to the stored atlas. -/
theorem relativeSpectrumDiagonalLocalMap₂_over (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalLocalMap₂ A p q ≫
        (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π =
      (relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₁ A p q)).left := by
  have hfst : relativeSpectrumDiagonalAtlasToSecond A p q ≫
      relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₂ A p q) =
        relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₁ A p q) := by
    apply yoneda.map_injective
    simp only [Functor.map_comp, relativeSpectrumDiagonalAtlasToSecond,
      relativeSpectrumPointAtlasToAtlas, Functor.relativelyRepresentable.fst',
      Functor.map_preimage, IsPullback.lift_fst]
  rw [relativeSpectrumDiagonalLocalMap₂, Category.assoc]
  exact (congrArg (fun f ↦ (relativeSpectrumDiagonalAtlasToSecond A p q).left ≫ f)
    (Scheme.relativeSpectrumPointMap_toBase _
      ⟨(relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₂ A p q)).left,
        relativeSpectrumPointAtlasAlgebraMap A (relativeSpectrumDiagonalBasePoint₂ A p q)⟩)).trans
    (congrArg (fun f ↦ f.left) hfst)

/-- The actual atlas cover of the coincidence base, viewed over the stored atlas scheme. -/
def relativeSpectrumDiagonalLocalSource (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    Over (atlasScheme X).left :=
  Over.mk (relativeSpectrumPointAtlasToAtlas A (relativeSpectrumDiagonalBasePoint₁ A p q)).left

/-- The first local spectrum map as a map over the stored atlas scheme. -/
def relativeSpectrumDiagonalLocalMap₁Over (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalLocalSource A p q ⟶
      Over.mk (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π :=
  Over.homMk (relativeSpectrumDiagonalLocalMap₁ A p q) (relativeSpectrumDiagonalLocalMap₁_over A p q)

/-- The second local spectrum map as a map over that same stored atlas scheme. -/
def relativeSpectrumDiagonalLocalMap₂Over (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalLocalSource A p q ⟶
      Over.mk (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π :=
  Over.homMk (relativeSpectrumDiagonalLocalMap₂ A p q) (relativeSpectrumDiagonalLocalMap₂_over A p q)

/-- The local coincidence scheme is the actual relative equalizer over the stored atlas scheme. -/
abbrev relativeSpectrumDiagonalLocalScheme (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    Scheme.{u} :=
  (equalizer (relativeSpectrumDiagonalLocalMap₁Over A p q)
    (relativeSpectrumDiagonalLocalMap₂Over A p q)).left

/-- The actual inclusion of the local coincidence scheme into the coincidence-base atlas. -/
def relativeSpectrumDiagonalLocalInclusion (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalLocalScheme A p q ⟶ (relativeSpectrumDiagonalAtlasOver A p q).left :=
  (equalizer.ι (relativeSpectrumDiagonalLocalMap₁Over A p q)
    (relativeSpectrumDiagonalLocalMap₂Over A p q)).left

/-- The local inclusion is closed by relative separatedness of the spectrum over the stored atlas. -/
theorem relativeSpectrumDiagonalLocal_isClosedImmersion (A : X.QcAlgebraUnder)
    (p q : relativeSpectrumPair A T) :
    AlgebraicGeometry.IsClosedImmersion (relativeSpectrumDiagonalLocalInclusion A p q) := by
  let hAffine : IsAffineHom
      (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π :=
    Scheme.isAffineHom_of_realizesRelativeSpectrum _ (Scheme.relativeSpectrumRealization_realizes _)
  let hSeparated := @AlgebraicGeometry.IsSeparated.of_isAffineHom _ _
    (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π hAffine
  exact @AlgebraicGeometry.isClosedImmersion_equalizer_ι_left (atlasScheme X).left
    (relativeSpectrumDiagonalLocalSource A p q)
    (Over.mk (Scheme.relativeSpectrumOver (QcAlgebraUnder.onChart A (relativeSpectrumAtlasChart X))).π)
    hSeparated (relativeSpectrumDiagonalLocalMap₁Over A p q) (relativeSpectrumDiagonalLocalMap₂Over A p q)

/-- The local equality ideal is the native kernel ideal of the actual relative equalizer inclusion. -/
def relativeSpectrumDiagonalLocalIdeal (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    (relativeSpectrumDiagonalAtlasOver A p q).left.IdealSheafData :=
  (relativeSpectrumDiagonalLocalInclusion A p q).ker

/-- The invariant local equality ideal descends by its native ideal-sheaf image on the base cover. -/
def relativeSpectrumDiagonalIdeal (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    (relativeSpectrumDiagonalBaseOver A p q).left.IdealSheafData :=
  (relativeSpectrumDiagonalLocalIdeal A p q).map (relativeSpectrumDiagonalAtlasToBase A p q).left

/-- Étale descent recovers the specified local equality ideal on the actual atlas pullback. -/
theorem relativeSpectrumDiagonalIdeal_comap (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    (relativeSpectrumDiagonalIdeal A p q).comap (relativeSpectrumDiagonalAtlasToBase A p q).left =
      relativeSpectrumDiagonalLocalIdeal A p q := sorry

/-- The actual scheme representing equality of the two original relative-spectrum points. -/
def relativeSpectrumDiagonalOver (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) : Over S :=
  Over.mk ((relativeSpectrumDiagonalIdeal A p q).subschemeι ≫
    (relativeSpectrumDiagonalBaseOver A p q).hom)

/-- The diagonal coincidence scheme's actual projection to the original test scheme. -/
def relativeSpectrumDiagonalToTest (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T) :
    relativeSpectrumDiagonalOver A p q ⟶ T :=
  Over.homMk
    ((relativeSpectrumDiagonalIdeal A p q).subschemeι ≫
      (relativeSpectrumDiagonalBaseToTest A p q).left) (by
        simp only [Category.assoc, Over.w]
        rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The equal-point hypotheses give the precise triangle into the stored base diagonal pullback. -/
theorem relativeSpectrumDiagonalBaseLift_w (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    {W : Over S} (a : W ⟶ T) (x : relativeSpectrumPair A W)
    (h : relativeSpectrumPairMap a p = x ∧ relativeSpectrumPairMap a q = x) :
    NatTrans.vcomp (relativeSpectrumPointBase A x) (CategoryTheory.Limits.diag X.functorOfPoints) =
      NatTrans.vcomp (yoneda.map a)
        (prod.lift (C := (Over S)ᵒᵖ ⥤ Type u) (relativeSpectrumPointBase A p : NatTrans (yoneda.obj T) X.functorOfPoints)
          (relativeSpectrumPointBase A q : NatTrans (yoneda.obj T) X.functorOfPoints)) := by
  have hp : (relativeSpectrumPointBase A x : NatTrans (yoneda.obj W) X.functorOfPoints) =
      NatTrans.vcomp (yoneda.map a) (relativeSpectrumPointBase A p) :=
    (congrArg (relativeSpectrumPointBase A) h.1).symm.trans (yonedaEquiv.symm_apply_apply _)
  have hq : (relativeSpectrumPointBase A x : NatTrans (yoneda.obj W) X.functorOfPoints) =
      NatTrans.vcomp (yoneda.map a) (relativeSpectrumPointBase A q) :=
    (congrArg (relativeSpectrumPointBase A) h.2).symm.trans (yonedaEquiv.symm_apply_apply _)
  change CategoryStruct.comp (obj := (Over S)ᵒᵖ ⥤ Type u)
      (relativeSpectrumPointBase A x) (CategoryTheory.Limits.diag X.functorOfPoints) =
    CategoryStruct.comp (obj := (Over S)ᵒᵖ ⥤ Type u) (yoneda.map a)
      (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))
  apply prod.hom_ext (C := (Over S)ᵒᵖ ⥤ Type u)
  · simp only [Category.assoc, prod.lift_fst, Category.comp_id]
    exact hp
  · simp only [Category.assoc, prod.lift_snd, Category.comp_id]
    exact hq

/-- Equal pulled-back original points give an actual lift to the stored base diagonal pullback. -/
def relativeSpectrumDiagonalBaseLift (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    {W : Over S} (a : W ⟶ T) (x : relativeSpectrumPair A W)
    (h : relativeSpectrumPairMap a p = x ∧ relativeSpectrumPairMap a q = x) :
    W ⟶ relativeSpectrumDiagonalBaseOver A p q :=
  yoneda.preimage
    ((X.representableDiagonal.isPullback
      (prod.lift (relativeSpectrumPointBase A p) (relativeSpectrumPointBase A q))).lift
      (relativeSpectrumPointBase A x) (yoneda.map a)
      (relativeSpectrumDiagonalBaseLift_w A p q a x h))

/-- Point equality gives the precise ideal-kernel containment needed by the native closed lift. -/
theorem relativeSpectrumDiagonalLift_ideal_le (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    {W : Over S} (a : W ⟶ T) (x : relativeSpectrumPair A W)
    (h : relativeSpectrumPairMap a p = x ∧ relativeSpectrumPairMap a q = x) :
    (relativeSpectrumDiagonalIdeal A p q).subschemeι.ker ≤
      (relativeSpectrumDiagonalBaseLift A p q a x h).left.ker := sorry

/-- The actual diagonal lift uses the concrete native subscheme and its specified ideal condition. -/
def relativeSpectrumDiagonalPointLift (A : X.QcAlgebraUnder) (p q : relativeSpectrumPair A T)
    {W : Over S} (a : W ⟶ T) (x : relativeSpectrumPair A W)
    (h : relativeSpectrumPairMap a p = x ∧ relativeSpectrumPairMap a q = x) :
    W ⟶ relativeSpectrumDiagonalOver A p q := by
  let I : (relativeSpectrumDiagonalBaseOver A p q).left.IdealSheafData :=
    relativeSpectrumDiagonalIdeal A p q
  let hI : AlgebraicGeometry.IsClosedImmersion I.subschemeι :=
    AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion _
      (I.range_subschemeι ▸ I.support.isClosed)
  exact Over.homMk
    (@AlgebraicGeometry.IsClosedImmersion.lift I.subscheme W.left
      (relativeSpectrumDiagonalBaseOver A p q).left I.subschemeι
      (relativeSpectrumDiagonalBaseLift A p q a x h).left hI
      (relativeSpectrumDiagonalLift_ideal_le A p q a x h)) (by
        letI : AlgebraicGeometry.IsClosedImmersion I.subschemeι := hI
        exact (AlgebraicGeometry.IsClosedImmersion.lift_fac_assoc I.subschemeι
          (relativeSpectrumDiagonalBaseLift A p q a x h).left
          (relativeSpectrumDiagonalLift_ideal_le A p q a x h)
          (relativeSpectrumDiagonalBaseOver A p q).hom).trans
          (relativeSpectrumDiagonalBaseLift A p q a x h).w)

end AlgebraicGeometry.AlgebraicSpace
