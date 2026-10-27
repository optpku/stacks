/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GermProperty.LocalRing
public import ReasLib.RingTheory.Etale.LocalProperty.Examples
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# Étale-local stalk properties

Noetherianity, dimension, regularity, discrete valuation, reducedness, normality,
Noetherian depth, Noetherian Cohen–Macaulayness, and Gorensteinness give étale-local
properties of scheme germs.
-/

@[expose] public section

universe u

open scoped ENat

namespace AlgebraicGeometry

/-- The germ property of having a Noetherian stalk is étale-local. -/
theorem ofLocalRing_isNoetherianRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsNoetherianRing R).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    constructor
    · intro h
      letI := h
      exact isNoetherianRing_of_ringEquiv R e
    · intro h
      letI := h
      exact isNoetherianRing_of_ringEquiv S e.symm
  · exact Algebra.Etale.localizationAtPrime_isNoetherianRing_iff

/-- The germ property of having stalk of Krull dimension `d` is étale-local. -/
theorem ofLocalRing_ringKrullDim_isEtaleLocal (d : WithBot ℕ∞) :
    (GermProperty.ofLocalRing fun R ↦ ringKrullDim R = d).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    change ringKrullDim R = d ↔ ringKrullDim S = d
    rw [ringKrullDim_eq_of_ringEquiv e]
  · intro A B _ _ _ _ q
    change ringKrullDim (Localization.AtPrime (q.asIdeal.under A)) = d ↔
      ringKrullDim (Localization.AtPrime q.asIdeal) = d
    rw [Algebra.Etale.ringKrullDim_localizationAtPrime_eq (A := A) q.asIdeal]

/-- The germ property of having a regular local stalk is étale-local. -/
theorem ofLocalRing_isRegularLocalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsRegularLocalRing R).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    constructor
    · intro h
      letI := h
      exact IsRegularLocalRing.of_ringEquiv e
    · intro h
      letI := h
      exact IsRegularLocalRing.of_ringEquiv e.symm
  · exact Algebra.Etale.localizationAtPrime_isRegularLocalRing_iff

/-- The germ property of having a discrete valuation stalk is étale-local. -/
theorem ofLocalRing_isDiscreteValuationRing_isEtaleLocal :
    (GermProperty.ofLocalRing LocalRingProperty.isDiscreteValuationLocalRing).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    constructor
    · rintro ⟨hR, hDVR⟩
      letI := hR
      letI := hDVR
      refine ⟨(MulEquiv.isDomain_iff e.toMulEquiv).mp hR, ?_⟩
      intro
      exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
    · rintro ⟨hS, hDVR⟩
      letI := hS
      letI := hDVR
      refine ⟨(MulEquiv.isDomain_iff e.toMulEquiv).mpr hS, ?_⟩
      intro
      exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
  · exact LocalRingProperty.isDiscreteValuationRing_isEtaleLocalAtPrimes

/-- The germ property of having a reduced stalk is étale-local. -/
theorem ofLocalRing_isReduced_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ _root_.IsReduced R).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    constructor
    · intro h
      letI := h
      exact isReduced_of_injective e.symm e.symm.injective
    · intro h
      letI := h
      exact isReduced_of_injective e e.injective
  · exact LocalRingProperty.isReduced_isEtaleLocalAtPrimes

/-- The germ property of having a normal stalk is étale-local. -/
theorem ofLocalRing_isNormalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsNormalRing R).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    exact IsNormalRing.iff_of_ringEquiv e
  · exact LocalRingProperty.isNormalRing_isEtaleLocalAtPrimes

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Ring equivalences identify regular sequences in the two maximal ideals. -/
private theorem moduleDepth_self_eq_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    moduleDepth R R = moduleDepth S S := by
  classical
  have hdepth (T : Type u) [CommRing T] [IsLocalRing T] :
      moduleDepth T T = sSup ((IsLocalRing.maximalIdeal T).regularSequenceLengths T) := by
    unfold moduleDepth Ideal.depth
    rw [if_neg]
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using
      (IsLocalRing.maximalIdeal.isMaximal T).ne_top
  rw [hdepth R, hdepth S]
  congr 1
  have hmap {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      (f : A ≃+* B) (n : ℕ∞)
      (hn : n ∈ (IsLocalRing.maximalIdeal A).regularSequenceLengths A) :
      n ∈ (IsLocalRing.maximalIdeal B).regularSequenceLengths B := by
    obtain ⟨rs, hrs, hmem, hlen⟩ := hn
    refine ⟨rs.map f, ?_, ?_, ?_⟩
    · simpa using (f.toSemilinearEquiv.isRegular_congr' rs).mp hrs
    · apply Ideal.span_le.mpr
      intro b hb
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact (IsLocalRing.mem_maximalIdeal (f a)).mpr
        ((map_mem_nonunits_iff f a).mpr
          ((IsLocalRing.mem_maximalIdeal a).mp (hmem (Ideal.subset_span ha))))
    · simpa using hlen
  ext n
  exact ⟨hmap e n, hmap e.symm n⟩

/-- The germ property of having a Noetherian stalk of depth `k` is étale-local. -/
theorem ofLocalRing_isNoetherianOfDepth_isEtaleLocal (k : ℕ) :
    (GermProperty.ofLocalRing (LocalRingProperty.isNoetherianOfDepth k)).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    change (IsNoetherianRing R ∧ moduleDepth R R = k) ↔
      (IsNoetherianRing S ∧ moduleDepth S S = k)
    constructor
    · rintro ⟨hN, hd⟩
      letI := hN
      exact ⟨isNoetherianRing_of_ringEquiv R e,
        (moduleDepth_self_eq_of_ringEquiv e) ▸ hd⟩
    · rintro ⟨hN, hd⟩
      letI := hN
      exact ⟨isNoetherianRing_of_ringEquiv S e.symm,
        (moduleDepth_self_eq_of_ringEquiv e.symm) ▸ hd⟩
  · exact LocalRingProperty.isNoetherianOfDepth_isEtaleLocalAtPrimes k

/-- The germ property of having a Noetherian Cohen–Macaulay stalk is étale-local. -/
theorem ofLocalRing_isNoetherianCohenMacaulay_isEtaleLocal :
    (GermProperty.ofLocalRing LocalRingProperty.isNoetherianCohenMacaulay).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    have hmap {A B : Type _} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
        (f : A ≃+* B) (h : LocalRingProperty.isNoetherianCohenMacaulay A) :
        LocalRingProperty.isNoetherianCohenMacaulay B := by
      obtain ⟨hN, hCM⟩ := h
      letI := hN
      refine ⟨isNoetherianRing_of_ringEquiv A f, ?_⟩
      intro
      letI := hCM
      refine ⟨?_⟩
      rw [Module.supportDim_self_eq_ringKrullDim,
        ← ringKrullDim_eq_of_ringEquiv f, ← moduleDepth_self_eq_of_ringEquiv f,
        ← Module.supportDim_self_eq_ringKrullDim]
      exact Module.CohenMacaulay.supportDim_eq_moduleDepth
    exact ⟨hmap e, hmap e.symm⟩
  · exact LocalRingProperty.isNoetherianCohenMacaulay_isEtaleLocalAtPrimes

open CategoryTheory in
/-- Restriction along a ring equivalence reflects the vanishing of Ext groups. -/
private theorem isGorensteinLocalRing_of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) [h : IsGorensteinLocalRing R] :
    IsGorensteinLocalRing S := by
  let F := ModuleCat.restrictScalars e.toRingHom
  letI : HasExt.{u} (ModuleCat.{u} R) := hasExt_of_enoughInjectives _
  letI : HasExt.{u} (ModuleCat.{u} S) := hasExt_of_enoughInjectives _
  refine ⟨isNoetherianRing_of_ringEquiv R e, ?_⟩
  obtain ⟨n, hn⟩ := (injectiveDimension_ne_top_iff (ModuleCat.of R R)).mp
    h.finiteSelfInjectiveDimension
  letI := hn
  haveI : HasInjectiveDimensionLE (F.obj (ModuleCat.of S S)) n :=
    hasInjectiveDimensionLT_of_iso (ModuleCat.restrictScalarsIsoOfEquiv e).symm (n + 1)
  refine (injectiveDimension_ne_top_iff (ModuleCat.of S S)).mpr ⟨n, ?_⟩
  apply HasInjectiveDimensionLT.mk
  intro i hi Y a
  apply (F.mapExt_bijective_of_preservesInjectiveObjects Y (ModuleCat.of S S) i).1
  simpa only [map_zero, CategoryTheory.Functor.mapExtAddHom_apply] using
    (Abelian.Ext.eq_zero_of_hasInjectiveDimensionLT (a.mapExactFunctor F) (n + 1) hi)

/-- The germ property of having a Gorenstein local stalk is étale-local. -/
theorem ofLocalRing_isGorensteinLocalRing_isEtaleLocal :
    (GermProperty.ofLocalRing fun R ↦ IsGorensteinLocalRing R).IsEtaleLocal := by
  apply GermProperty.ofLocalRing.isEtaleLocal
  · intro R S _ _ _ _ e
    constructor
    · intro h
      letI := h
      exact isGorensteinLocalRing_of_ringEquiv e
    · intro h
      letI := h
      exact isGorensteinLocalRing_of_ringEquiv e.symm
  · exact LocalRingProperty.isGorensteinLocalRing_isEtaleLocalAtPrimes

end AlgebraicGeometry
