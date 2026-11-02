/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# Adic completion of an affine algebraization setup

This file records the ring, ideals, affine scheme, and punctured-open morphism obtained by
completing an affine algebraization setup along its distinguished ideal.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

private lemma completion_comap_ofIdealTop {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    (I : Y.IdealSheafData) :
    I.comap f = Scheme.IdealSheafData.ofIdealTop
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom) := by
  have hle {Z : Scheme.{u}} [IsAffine Z] (I J : Z.IdealSheafData) :
      I ≤ J ↔ I.ideal ⟨⊤, isAffineOpen_top Z⟩ ≤ J.ideal ⟨⊤, isAffineOpen_top Z⟩ :=
    ⟨fun h ↦ h _, Scheme.IdealSheafData.le_of_isAffine⟩
  apply eq_of_forall_ge_iff
  intro J
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, hle, hle]
  rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
  simp [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_le_iff_le_comap,
    Scheme.Hom.appTop]
  rfl

omit [IsNoetherianRing A] in
private lemma completion_comap_idealOnSpec
    {B : Type u} [CommRing B] (I : Ideal A) (f : A →+* B) :
    (Scheme.idealSheafDataOfIdealOnSpec I).comap
      (Spec.map (CommRingCat.ofHom f)) =
      Scheme.idealSheafDataOfIdealOnSpec (I.map f) := by
  rw [completion_comap_ofIdealTop]
  apply Scheme.IdealSheafData.ext_of_isAffine
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal, homOfLE_refl, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id, Ideal.map_id]
  change (I.comap (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv).map
      (Spec.map (CommRingCat.ofHom f)).appTop.hom =
    (I.map f).comap (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv
  rw [← Ideal.map_symm (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv,
    ← Ideal.map_symm (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv]
  change (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
      (Spec.map (CommRingCat.ofHom f)).appTop.hom =
    (I.map f).map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

/-- The completed ring `A'` associated to an affine algebraization setup. -/
abbrev completionRing (S : AffineAlgebraizationSetup A) : Type u :=
  AdicCompletion S.I A

/-- The extended ideal `I'` in the completed ring. -/
def completionIdeal (S : AffineAlgebraizationSetup A) : Ideal S.completionRing :=
  S.I.map (algebraMap A S.completionRing)

/-- The extended ideal `a'` in the completed ring. -/
def completionClosedIdeal (S : AffineAlgebraizationSetup A) : Ideal S.completionRing :=
  S.a.map (algebraMap A S.completionRing)

/-- The affine scheme `X' = Spec(A')` of the completed ring. -/
abbrev completionSpec (S : AffineAlgebraizationSetup A) : Scheme :=
  Spec (CommRingCat.of S.completionRing)

/-- The morphism `X' ⟶ X` induced by the completion homomorphism `A ⟶ A'`. -/
def completionMap (S : AffineAlgebraizationSetup A) : S.completionSpec ⟶ S.X :=
  Spec.map (CommRingCat.ofHom (algebraMap A S.completionRing))

/-- The punctured open `U'`, represented canonically as the inverse image of `U` in `X'`. -/
def completionOpen (S : AffineAlgebraizationSetup A) : S.completionSpec.Opens :=
  S.completionMap ⁻¹ᵁ S.U

/-- The inverse-image model of `U'` is the complement of the support of `a'`. -/
theorem completionOpen_eq_complement (S : AffineAlgebraizationSetup A) :
    S.completionOpen =
      (Scheme.idealSheafDataOfIdealOnSpec S.completionClosedIdeal).openComplement := by
  change (Spec.map (CommRingCat.ofHom (algebraMap A S.completionRing))) ⁻¹ᵁ
      (Scheme.idealSheafDataOfIdealOnSpec S.a).support.compl =
    (Scheme.idealSheafDataOfIdealOnSpec
      (S.a.map (algebraMap A S.completionRing))).support.compl
  rw [← completion_comap_idealOnSpec, Scheme.IdealSheafData.support_comap]
  rfl

/-- The punctured open in the completed affine scheme is Noetherian. -/
def isNoetherianCompletionOpen (S : AffineAlgebraizationSetup A) :
    IsNoetherian S.completionOpen := by
  infer_instance

/-- The restriction `U' ⟶ U` of the completion morphism. -/
def completionOpenMap (S : AffineAlgebraizationSetup A) :
    S.completionOpen.toScheme ⟶ S.U.toScheme :=
  S.completionMap ∣_ S.U

/-- The restricted completion morphism commutes with the two open immersions. -/
theorem completionOpenMap_comp_ι (S : AffineAlgebraizationSetup A) :
    S.completionOpenMap ≫ S.U.ι = S.completionOpen.ι ≫ S.completionMap := by
  change (S.completionMap ∣_ S.U) ≫ S.U.ι =
    (S.completionMap ⁻¹ᵁ S.U).ι ≫ S.completionMap
  exact AlgebraicGeometry.morphismRestrict_ι S.completionMap S.U

/-- The pullback of `I 𝒪_U` to the completed punctured open `U'`. -/
def completionIdealOnOpen (S : AffineAlgebraizationSetup A) :
    S.completionOpen.toScheme.IdealSheafData :=
  ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).comap S.completionOpenMap

/-- The pulled-back ideal on `U'` is the restriction of the ideal sheaf associated to `I'`. -/
theorem completionIdealOnOpen_eq (S : AffineAlgebraizationSetup A) :
    S.completionIdealOnOpen =
      (Scheme.idealSheafDataOfIdealOnSpec S.completionIdeal).comap S.completionOpen.ι := by
  unfold completionIdealOnOpen
  rw [← Scheme.IdealSheafData.comap_comp, S.completionOpenMap_comp_ι,
    Scheme.IdealSheafData.comap_comp]
  congr 1
  exact completion_comap_idealOnSpec S.I (algebraMap A S.completionRing)

/-- The affine completion morphism is flat. -/
def flatCompletionMap (S : AffineAlgebraizationSetup A) :
    Flat S.completionMap := by
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap A S.completionRing)))
  rw [AlgebraicGeometry.Flat.SpecMap_iff]
  change (algebraMap A S.completionRing).Flat
  rw [RingHom.flat_algebraMap_iff]
  infer_instance

/-- The completion morphism restricted to `U'` is flat. -/
def flatCompletionOpenMap (S : AffineAlgebraizationSetup A) :
    Flat S.completionOpenMap := by
  change Flat (S.completionMap ∣_ S.U)
  letI := S.flatCompletionMap
  infer_instance

/-- The completed ring is complete along the extended ideal `I'`. -/
def isAdicCompleteCompletionRing (S : AffineAlgebraizationSetup A) :
    IsAdicComplete S.completionIdeal S.completionRing := by
  exact AdicCompletion.isAdicComplete_self S.I S.I.fg_of_isNoetherianRing

/-- The closed subscheme of `U'` cut out by the pulled-back ideal maps isomorphically to the
closed subscheme of `U` cut out by `I 𝒪_U`. -/
def isIsoCompletionOpenSubschemeMap (S : AffineAlgebraizationSetup A) :
    IsIso (Scheme.IdealSheafData.subschemeMap S.completionIdealOnOpen
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι) S.completionOpenMap
      (((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι).le_map_comap
        S.completionOpenMap)) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
