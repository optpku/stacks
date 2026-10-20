/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Quotients of residue-identified Artinian local algebras

Ideals contained in the maximal ideal give quotient objects with canonical
projections and factor maps for morphisms that annihilate the ideal.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The kernel of a morphism of Artinian local algebras lies in the source maximal ideal. -/
theorem ker_le_maximal {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A) :
    RingHom.ker f.hom.toRingHom ≤ maximalIdeal B.carrier :=
  le_maximalIdeal (RingHom.ker_ne_top f.hom.toRingHom)

/-- The quotient by an ideal contained in the maximal ideal is nontrivial. -/
theorem nontrivial_quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : Nontrivial (B.carrier ⧸ J) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (mt (fun h ↦ eq_top_iff.2 (h.symm.trans_le hJ)) (Ideal.IsMaximal.ne_top inferInstance))

/-- The quotient by an ideal contained in the maximal ideal is local. -/
theorem isLocalRing_quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : IsLocalRing (B.carrier ⧸ J) :=
  @IsLocalRing.of_surjective' B.carrier (B.carrier ⧸ J) inferInstance inferInstance inferInstance
    (nontrivial_quotient B J hJ) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

/-- Every quotient of an Artinian local algebra is Artinian. -/
theorem isArtinianRing_quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier) :
    IsArtinianRing (B.carrier ⧸ J) :=
  inferInstance

/-- The residue identification of a local algebra induces one on its proper quotients. -/
noncomputable def quotientResidueFieldIso (B : ArtinianLocalAlgCat Λ k)
    (J : Ideal B.carrier) (hJ : J ≤ maximalIdeal B.carrier)
    (hloc : IsLocalRing (B.carrier ⧸ J)) :
    @AlgEquiv Λ (@ResidueField (B.carrier ⧸ J) inferInstance hloc) k _ _ _
      (@ResidueField.algebra (B.carrier ⧸ J) inferInstance hloc Λ inferInstance inferInstance)
      inferInstance :=
  (Ideal.quotientEquivAlgOfEq Λ
      (@IsLocalRing.map_maximalIdeal_of_surjective B.carrier (B.carrier ⧸ J)
        inferInstance inferInstance inferInstance hloc
        (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ hJ).trans B.residueFieldIso)

/-- Quotient an Artinian local algebra by an ideal contained in its maximal ideal. -/
noncomputable def quotient (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : ArtinianLocalAlgCat Λ k :=
  ⟨CommRingCat.of (B.carrier ⧸ J), inferInstance,
    isLocalRing_quotient B J hJ, isArtinianRing_quotient B J,
    quotientResidueFieldIso B J hJ (isLocalRing_quotient B J hJ)⟩

/-- The carrier of the categorical quotient is the specified ideal quotient. -/
theorem quotient_carrier (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    (B.quotient J hJ).carrier = (B.carrier ⧸ J) := sorry

/-- The categorical quotient is Artinian local with the induced residue identification. -/
theorem quotient_spec (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    IsArtinianRing (B.quotient J hJ).carrier ∧ IsLocalRing (B.quotient J hJ).carrier ∧
      (B.quotient J hJ).residueFieldIso =
        quotientResidueFieldIso B J hJ (isLocalRing_quotient B J hJ) := sorry

/-- The canonical algebra quotient map is local. -/
theorem quotientMk_isLocalHom (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    IsLocalHom (Ideal.Quotient.mkₐ Λ J : algebraHom B (B.quotient J hJ)) := sorry

/-- The canonical quotient map respects the induced residue identification. -/
theorem quotientMk_residue_compat (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    residueCompat (A := B) (B := B.quotient J hJ)
      (Ideal.Quotient.mkₐ Λ J) (quotientMk_isLocalHom B J hJ) = residueIsoHom B := sorry

/-- The canonical projection to the residue-identified categorical quotient. -/
noncomputable def quotientMk (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) : B ⟶ B.quotient J hJ :=
  Hom.of (Ideal.Quotient.mkₐ Λ J)
    (quotientMk_isLocalHom B J hJ) (quotientMk_residue_compat B J hJ)

/-- The underlying algebra map of the categorical projection is the quotient map. -/
theorem quotientMk_hom (B : ArtinianLocalAlgCat Λ k) (J : Ideal B.carrier)
    (hJ : J ≤ maximalIdeal B.carrier) :
    (quotientMk B J hJ).hom = Ideal.Quotient.mkₐ Λ J := sorry

/-- The induced algebra map through an ideal contained in the kernel is local. -/
theorem quotientFactor_isLocalHom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    IsLocalHom (Ideal.Quotient.liftₐ J f.hom
      fun element hElement ↦ RingHom.mem_ker.mp (hJ hElement) :
        algebraHom (B.quotient J (hJ.trans (ker_le_maximal f))) A) := sorry

/-- The induced quotient factor map respects the chosen residue identifications. -/
theorem quotientFactor_residue_compat {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    residueCompat (A := B.quotient J (hJ.trans (ker_le_maximal f))) (B := A)
      (Ideal.Quotient.liftₐ J f.hom fun element hElement ↦ RingHom.mem_ker.mp (hJ hElement))
      (quotientFactor_isLocalHom f J hJ) =
        residueIsoHom (B.quotient J (hJ.trans (ker_le_maximal f))) := sorry

/-- Factor a morphism through the quotient by an ideal contained in its kernel. -/
noncomputable def quotientFactor {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    B.quotient J (hJ.trans (ker_le_maximal f)) ⟶ A :=
  Hom.of (Ideal.Quotient.liftₐ J f.hom
      fun element hElement ↦ RingHom.mem_ker.mp (hJ hElement))
    (quotientFactor_isLocalHom f J hJ) (quotientFactor_residue_compat f J hJ)

/-- The underlying algebra map of the categorical factor is the induced quotient map. -/
theorem quotientFactor_hom {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    (quotientFactor f J hJ).hom =
      Ideal.Quotient.liftₐ J f.hom fun element hElement ↦ RingHom.mem_ker.mp (hJ hElement) := sorry

/-- The canonical projection followed by the quotient factor recovers the original morphism. -/
theorem quotientFactor_comp_mk {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A)
    (J : Ideal B.carrier) (hJ : J ≤ RingHom.ker f.hom.toRingHom) :
    quotientMk B J (hJ.trans (ker_le_maximal f)) ≫ quotientFactor f J hJ = f := sorry

end ArtinianLocalAlgCat
