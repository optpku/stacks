/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local
public import ReasLib.NumberTheory.NumberField.Ramification.Loci

/-!
# Étale covers from extensions of number fields

This file defines the morphism on spectra of rings of integers and its restriction over the
relative discriminant complement, together with the corresponding ramification properties.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped NumberField

noncomputable section

universe u

namespace NumberField.Ramification

variable (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The morphism on spectra induced by the inclusion of rings of integers. -/
def specMap : Spec (.of (𝓞 L)) ⟶ Spec (.of (𝓞 K)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 K) (𝓞 L)))

/-- On points, the spectrum morphism is contraction of prime ideals. -/
theorem specMap_apply (p : PrimeSpectrum (𝓞 L)) :
    specMap K L p = PrimeSpectrum.comap (algebraMap (𝓞 K) (𝓞 L)) p := rfl

/-- The restriction of the spectrum morphism over the relative discriminant complement. -/
def cover : (specMap K L ⁻¹ᵁ discriminantOpen K L).toScheme ⟶ discriminantOpen K L :=
  specMap K L ∣_ discriminantOpen K L

/-- Composing the restricted cover with its target open immersion recovers the spectrum
morphism on the inverse-image open. -/
theorem cover_comp_ι :
    cover K L ≫ (discriminantOpen K L).ι =
      (specMap K L ⁻¹ᵁ discriminantOpen K L).ι ≫ specMap K L :=
  morphismRestrict_ι _ _

private theorem specMap_stalkMap_formallyUnramified_iff
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum S) :
    ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap p).hom.FormallyUnramified ↔
      Algebra.IsUnramifiedAt R p.asIdeal := by
  rw [RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap R S)) p)]
  letI := Localization.AtPrime.algebraOfLiesOver (p.asIdeal.under R) p.asIdeal
  change Algebra.FormallyUnramified (Localization.AtPrime (p.asIdeal.under R))
      (Localization.AtPrime p.asIdeal) ↔
    Algebra.FormallyUnramified R (Localization.AtPrime p.asIdeal)
  constructor <;> intro h <;> letI := h
  · exact Algebra.FormallyUnramified.comp R (Localization.AtPrime (p.asIdeal.under R)) _
  · exact Algebra.FormallyUnramified.of_restrictScalars R _ _

/-- Scheme-theoretic unramifiedness of the spectrum morphism at a prime is equivalent to
conventional unramifiedness of the corresponding extension of local rings. -/
theorem specMap_unramifiedAt_iff (p : PrimeSpectrum (𝓞 L)) :
    (specMap K L).UnramifiedAt p ↔ Algebra.IsUnramifiedAt (𝓞 K) p.asIdeal := by
  have : LocallyOfFiniteType (specMap K L) := by
    rw [specMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  constructor
  · rintro ⟨V, U, hp, e, h⟩
    letI := h
    apply (specMap_stalkMap_formallyUnramified_iff (R := 𝓞 K) p).mp
    exact (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      ((specMap K L).resLEStalkMap e ⟨p, hp⟩)).mp
      (FormallyUnramified.stalkMap _ _)
  · intro hp
    letI := hp
    obtain ⟨r, hr, h⟩ := Algebra.exists_formallyUnramified_of_isUnramifiedAt
      (R := 𝓞 K) p.asIdeal
    refine ⟨⟨⊤, isAffineOpen_top _⟩,
      ⟨PrimeSpectrum.basicOpen r,
        IsAffineOpen.Spec_basicOpen (R := .of (𝓞 L)) r⟩, hr, by simp, ?_⟩
    refine { toFormallyUnramified := ?_, toLocallyOfFiniteType := inferInstance }
    apply HasRingHomProperty.of_stalkMap (P := @FormallyUnramified)
      RingHom.FormallyUnramified.ofLocalizationPrime
    intro x
    apply (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      ((specMap K L).resLEStalkMap _ x)).mpr
    apply (specMap_stalkMap_formallyUnramified_iff (R := 𝓞 K) x.val).mpr
    exact Algebra.basicOpen_subset_unramifiedLocus_iff.mpr h x.property

set_option backward.isDefEq.respectTransparency false in
/-- The morphism from the complement of the different to the base spectrum is unramified. -/
@[instance]
theorem differentCoverUnramified :
    Unramified ((differentOpen K L).ι ≫ specMap K L) := by
  have hft : LocallyOfFiniteType (specMap K L) := by
    rw [specMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : FormallyUnramified (differentOpen K L).ι :=
    HasRingHomProperty.of_isOpenImmersion
      RingHom.FormallyUnramified.holdsForLocalizationAway.containsIdentities
  have hft' : LocallyOfFiniteType ((differentOpen K L).ι ≫ specMap K L) :=
    locallyOfFiniteType_comp _ _
      (hf := locallyOfFiniteType_of_isOpenImmersion _) (hg := hft)
  refine { toFormallyUnramified := ?_, toLocallyOfFiniteType := hft' }
  apply HasRingHomProperty.of_stalkMap (P := @FormallyUnramified)
    RingHom.FormallyUnramified.ofLocalizationPrime
  intro x
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  apply RingHom.FormallyUnramified.comp
  · apply (specMap_stalkMap_formallyUnramified_iff (R := 𝓞 K) x.val).mpr
    apply not_dvd_differentIdeal_iff.mp
    rw [Ideal.dvd_iff_le]
    exact x.property
  · exact FormallyUnramified.stalkMap _ _

/-- The morphism from the complement of the different to the base spectrum is flat. -/
@[instance]
theorem differentCoverFlat : Flat ((differentOpen K L).ι ≫ specMap K L) := by
  have : Flat (specMap K L) := by
    rw [specMap, Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  infer_instance

/-- The morphism from the complement of the different to the base spectrum is étale. -/
@[instance]
theorem differentCoverEtale : Etale ((differentOpen K L).ι ≫ specMap K L) := by
  have : LocallyOfFinitePresentation (specMap K L) := by
    rw [specMap, LocallyOfFinitePresentation.SpecMap_iff]
    exact RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
  exact Etale.of_formallyUnramified_of_flat _

open UniqueFactorizationMonoid in
private theorem exists_primeOver_le_of_relNorm_le (I : Ideal (𝓞 L)) (hI : I ≠ ⊥)
    (p : PrimeSpectrum (𝓞 K)) (h : Ideal.relNorm (𝓞 K) I ≤ p.asIdeal) :
    ∃ Q : Ideal (𝓞 L), Q.IsPrime ∧ Q.LiesOver p.asIdeal ∧ I ≤ Q := by
  classical
  have hprod : ((normalizedFactors I).map (Ideal.relNorm (𝓞 K))).prod ≤ p.asIdeal := by
    rw [← map_multiset_prod, Ideal.prod_normalizedFactors_eq_self hI]
    exact h
  obtain ⟨Q, hQ, hN⟩ :=
    (p.isPrime.multiset_prod_map_le (Ideal.relNorm (𝓞 K))).mp hprod
  obtain ⟨hQprime, hIQ⟩ := (Ideal.mem_normalizedFactors_iff hI).mp hQ
  letI := hQprime
  have : Q.IsMaximal := hQprime.isMaximal (ne_zero_of_mem_normalizedFactors hQ)
  have hpow : Q.under (𝓞 K) ^ Q.inertiaDeg (𝓞 K) ≤ p.asIdeal := by
    rwa [← Ideal.relNorm_eq_pow_of_isMaximal Q (Q.under (𝓞 K))]
  have hqe : Q.under (𝓞 K) = p.asIdeal :=
    Ideal.IsMaximal.eq_of_le inferInstance p.isPrime.ne_top
      (Ideal.IsPrime.le_of_pow_le hpow)
  exact ⟨Q, hQprime, ⟨hqe.symm⟩, hIQ⟩

/-- For a Galois extension, the inverse image of the discriminant complement is the complement
of the different. -/
theorem preimageDiscriminantOpen_eq_differentOpen [IsGalois K L] :
    specMap K L ⁻¹ᵁ discriminantOpen K L = differentOpen K L := by
  ext p
  change (¬ Ideal.relNorm (𝓞 K) (differentIdeal (𝓞 K) (𝓞 L)) ≤
      p.asIdeal.under (𝓞 K)) ↔
    ¬ differentIdeal (𝓞 K) (𝓞 L) ≤ p.asIdeal
  constructor
  · intro h hd
    exact h ((Ideal.relNorm_mono (𝓞 K) hd).trans
      (Ideal.relNorm_le_comap (𝓞 K) p.asIdeal))
  · intro h hn
    have hunr : Algebra.IsUnramifiedAt (𝓞 K) p.asIdeal :=
      not_dvd_differentIdeal_iff.mp (by simpa only [Ideal.dvd_iff_le] using h)
    obtain ⟨Q, hQ, hQp, hDQ⟩ := exists_primeOver_le_of_relNorm_le K L
      (differentIdeal (𝓞 K) (𝓞 L)) differentIdeal_ne_bot
      (PrimeSpectrum.comap (algebraMap (𝓞 K) (𝓞 L)) p) hn
    letI := hQ
    have : Q.LiesOver (p.asIdeal.under (𝓞 K)) := hQp
    have he := Ideal.ramificationIdx_eq_of_isGaloisGroup
      (p.asIdeal.under (𝓞 K)) p.asIdeal Q (L ≃ₐ[K] L)
    have huQ : Algebra.IsUnramifiedAt (𝓞 K) Q :=
      Ideal.ramificationIdx_eq_one_iff.mp
        (he.symm.trans (Ideal.ramificationIdx_eq_one_iff.mpr hunr))
    exact (not_dvd_differentIdeal_iff.mpr huQ) (Ideal.dvd_iff_le.mpr hDQ)

/-- The cover over the discriminant complement of a Galois extension is finite. -/
@[instance]
theorem galoisCoverFinite [IsGalois K L] : IsFinite (cover K L) := by
  have : IsFinite (specMap K L) := by
    rw [specMap, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  unfold cover
  infer_instance

/-- The cover over the discriminant complement of a Galois extension is étale. -/
@[instance]
theorem galoisCoverEtale [IsGalois K L] : Etale (cover K L) := by
  have : Etale (cover K L ≫ (discriminantOpen K L).ι) := by
    rw [cover_comp_ι, preimageDiscriminantOpen_eq_differentOpen]
    infer_instance
  have : LocallyOfFiniteType (discriminantOpen K L).ι :=
    locallyOfFiniteType_of_isOpenImmersion _
  have : FormallyUnramified (discriminantOpen K L).ι :=
    HasRingHomProperty.of_isOpenImmersion
      RingHom.FormallyUnramified.holdsForLocalizationAway.containsIdentities
  exact Etale.of_comp _ (discriminantOpen K L).ι

/-- The cover over the discriminant complement of a Galois extension is surjective. -/
@[instance]
theorem galoisCoverSurjective [IsGalois K L] : Surjective (cover K L) := by
  have : Surjective (specMap K L) := ⟨Algebra.IsIntegral.comap_surjective _ _⟩
  exact IsZariskiLocalAtTarget.restrict ‹Surjective (specMap K L)› _

end NumberField.Ramification
