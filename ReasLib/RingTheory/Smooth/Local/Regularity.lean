/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Unramified.LocalStructure
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regularity of formally smooth local algebras

This leaf records the local regularity consequence of formal smoothness at
the essentially finite-type level.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Algebra.FormallySmooth

private theorem ringKrullDim_le_of_flat_localHom
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] : ringKrullDim R ≤ ringKrullDim S := by
  haveI : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm⟩
  change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
  apply iSup_le
  intro l
  obtain ⟨P, _, hP, hPover⟩ := Ideal.exists_ideal_le_liesOver_of_le (maximalIdeal S)
    (q := maximalIdeal R) (p := l.last.asIdeal)
    (IsLocalRing.le_maximalIdeal l.last.isPrime.ne_top)
  haveI : P.IsPrime := hP
  haveI : P.LiesOver l.last.asIdeal := hPover
  obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  exact hlen ▸ Order.LTSeries.length_le_krullDim L

private theorem isRegularLocalRing_of_flat_formallyUnramified
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) =
        ((Ideal.map (algebraMap R S) (maximalIdeal R)).spanFinrank : WithBot ℕ∞) := by
      rw [Algebra.FormallyUnramified.map_maximalIdeal]
    _ ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := ringKrullDim_le_of_flat_localHom

private theorem isRegularLocalRing_localization_of_etale
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R] [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let p := q.under R
  letI := Localization.AtPrime.algebraOfLiesOver p q
  haveI : Algebra.FormallyUnramified R (Localization.AtPrime q) := inferInstance
  haveI : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.localization_base p.primeCompl
  haveI : Algebra.EssFiniteType R (Localization.AtPrime q) := inferInstance
  haveI : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  haveI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  exact isRegularLocalRing_of_flat_formallyUnramified (R := Localization.AtPrime p)

/-- An essentially finite-type formally smooth local algebra over a field is regular. -/
@[stacks 00TT "regularity of formally smooth local algebras over fields"]
theorem isRegularLocalRing
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [IsLocalRing A] [Algebra.EssFiniteType k A] [Algebra.FormallySmooth k A] :
    IsRegularLocalRing A := by
  -- Realize the local algebra as a prime localization of its finite-type model.
  let S := Algebra.EssFiniteType.subalgebra k A
  let p : Ideal S := (maximalIdeal A).comap (algebraMap S A)
  haveI : p.IsPrime := inferInstance
  haveI : IsLocalization.AtPrime A p := by
    change IsLocalization p.primeCompl A
    have hm : p.primeCompl = Algebra.EssFiniteType.submonoid k A := by
      ext x
      change (¬ ¬ IsUnit (algebraMap S A x)) ↔ IsUnit (algebraMap S A x)
      exact not_not
    rw [hm]
    infer_instance
  haveI : Algebra.IsSmoothAt k p :=
    Algebra.FormallySmooth.of_equiv
      ((IsLocalization.algEquiv p.primeCompl A (Localization.AtPrime p)).restrictScalars k)
  haveI : Algebra.FinitePresentation k S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- Smoothness gives a standard étale chart over a polynomial ring, which is regular.
  obtain ⟨f, hf, n, alg, tower, etale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let B := Localization.Away f
  let P := MvPolynomial (Fin n) k
  letI : Algebra P B := alg
  letI : IsScalarTower k P B := tower
  letI : Algebra.IsStandardEtale P B := etale
  let q : Ideal B := p.map (algebraMap S B)
  have hd : Disjoint (Submonoid.powers f : Set S) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) B p
    inferInstance hd
  have hqp : q.comap (algebraMap S B) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) B inferInstance hd
  haveI : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have hm : (q.comap (algebraMap S B)).primeCompl = p.primeCompl := by
      ext y
      change (y ∉ q.comap (algebraMap S B)) ↔ (y ∉ p)
      rw [hqp]
    change IsLocalization p.primeCompl (Localization.AtPrime q)
    rw [← hm]
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (.powers f) (Localization.AtPrime q) q
  haveI : IsRegularLocalRing (Localization.AtPrime q) := isRegularLocalRing_localization_of_etale
    (R := P) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime q) A).toRingEquiv

end Algebra.FormallySmooth
