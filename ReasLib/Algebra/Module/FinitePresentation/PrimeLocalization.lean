/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Weak

/-!
# Finite presentation detected by prime localizations

This leaf owns the finite family of prime localizations which detects equality, together with
the flat finite-presentation descent criteria for polynomial modules and finite-type algebras.

@stack 053A
@stack 053B
@stack 05GS
-/

@[expose] public section

open scoped TensorProduct

-- Local instance justification (instance diamond): use the polynomial right-factor action in
-- the iterated tensor product occurring in the localized module statement.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

namespace PrimeLocalization

/-- A finite family of prime localizations of `R` detects equality when the diagonal map from
`R` to their dependent product is injective. -/
@[stacks 05GS "prime localizations detecting equality"]
def DetectsEquality (R : Type u) [CommRing R] : Prop :=
  ∃ s : Finset (PrimeSpectrum R),
    Function.Injective
      (fun r : R ↦ fun p : s ↦ algebraMap R (Localization.AtPrime p.1.asIdeal) r)

namespace DetectsEquality

-- A nonzero element survives at any prime containing its annihilator.
private theorem of_finite_primes (R : Type u) [CommRing R]
    (s : Set (Ideal R)) (hs : s.Finite)
    (hprime : ∀ p ∈ s, p.IsPrime)
    (hcover : ∀ r : R, r ≠ 0 → ∃ p ∈ s, Ideal.torsionOf R R r ≤ p) :
    PrimeLocalization.DetectsEquality R := by
  classical
  have hfinite : (PrimeSpectrum.asIdeal ⁻¹' s).Finite :=
    hs.preimage (fun _ _ _ _ h ↦ PrimeSpectrum.ext h)
  refine ⟨hfinite.toFinset, ?_⟩
  intro a b hab
  apply sub_eq_zero.mp
  by_contra hne
  obtain ⟨p, hp, hAnn⟩ := hcover (a - b) hne
  letI : p.IsPrime := hprime p hp
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hq : q ∈ hfinite.toFinset := hfinite.mem_toFinset.mpr hp
  have heq := congrFun hab ⟨q, hq⟩
  have hzero : algebraMap R (Localization.AtPrime p) (a - b) = 0 := by
    simpa only [map_sub, sub_eq_zero] using heq
  obtain ⟨t, ht⟩ :=
    (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) (a - b)).mp hzero
  exact t.2 (hAnn ((Ideal.mem_torsionOf_iff _ _).mpr ht))

/-- Remark 15.25.5 (1): a local ring has a finite family of prime localizations which detects
equality. -/
@[stacks 05GS "Remark 15.25.5 (1)"]
theorem ofIsLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    PrimeLocalization.DetectsEquality R := by
  apply of_finite_primes R {IsLocalRing.maximalIdeal R} (Set.finite_singleton _)
  · intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    infer_instance
  · intro r hr
    refine ⟨IsLocalRing.maximalIdeal R, Set.mem_singleton _, ?_⟩
    exact IsLocalRing.le_maximalIdeal (fun h ↦ hr ((Ideal.torsionOf_eq_top_iff R r).mp h))

/-- Remark 15.25.5 (2): a Noetherian ring has a finite family of prime localizations which
detects equality. -/
@[stacks 05GS "Remark 15.25.5 (2)"]
theorem ofIsNoetherianRing (R : Type u) [CommRing R] [IsNoetherianRing R] :
    PrimeLocalization.DetectsEquality R := by
  apply of_finite_primes R (associatedPrimes R R) (associatedPrimes.finite R R)
  · intro p hp
    exact hp.isPrime
  · intro r hr
    obtain ⟨p, hp, hAnn⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R r hr
    exact ⟨p, hp, by simpa only [Ideal.colon_bot_singleton_eq_torsionOf] using hAnn⟩

/-- Remark 15.25.5 (3): a domain has a finite family of prime localizations which detects
equality. -/
@[stacks 05GS "Remark 15.25.5 (3)"]
theorem ofIsDomain (R : Type u) [CommRing R] [IsDomain R] :
    PrimeLocalization.DetectsEquality R := by
  apply of_finite_primes R {⊥} (Set.finite_singleton _)
  · intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    infer_instance
  · intro r hr
    refine ⟨⊥, Set.mem_singleton _, ?_⟩
    exact ((Ideal.torsionOf_eq_bot_iff_of_noZeroSMulDivisors R r).mpr hr).le

/-- Remark 15.25.5 (4): a reduced ring with finitely many minimal primes has a finite family of
prime localizations which detects equality. -/
@[stacks 05GS "Remark 15.25.5 (4)"]
theorem ofIsReducedOfFiniteMinimalPrimes
    (R : Type u) [CommRing R] [IsReduced R] (hfinite : (minimalPrimes R).Finite) :
    PrimeLocalization.DetectsEquality R := by
  apply of_finite_primes R (minimalPrimes R) hfinite
  · intro p hp
    exact hp.isPrime
  · intro r hr
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes
      (I := Ideal.torsionOf R R r) (fun h ↦ hr ((Ideal.torsionOf_eq_top_iff R r).mp h))
    have hweak : p ∈ weaklyAssociatedPrimes R R := ⟨r, hp⟩
    rw [weaklyAssociatedPrimes.ring_eq_minimalPrimes] at hweak
    exact ⟨p, hweak, hp.le⟩

/-- Remark 15.25.5 (5): a ring with finitely many weakly associated primes has a finite family
of prime localizations which detects equality. -/
@[stacks 05GS "Remark 15.25.5 (5)"]
theorem ofFiniteWeaklyAssociatedPrimes
    (R : Type u) [CommRing R] (hfinite : (weaklyAssociatedPrimes R R).Finite) :
    PrimeLocalization.DetectsEquality R := by
  apply of_finite_primes R (weaklyAssociatedPrimes R R) hfinite
  · intro p hp
    exact hp.isPrime
  · intro r hr
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes
      (I := Ideal.torsionOf R R r) (fun h ↦ hr ((Ideal.torsionOf_eq_top_iff R r).mp h))
    exact ⟨p, ⟨r, hp⟩, hp.le⟩

end DetectsEquality

end PrimeLocalization

namespace Module.FinitePresentation

/-- Lemma 15.25.1: a finite module over a finite-variable polynomial ring, flat over the base,
is finitely presented when all of its prime-local base changes are finitely presented and a
finite family of base-prime localizations detects equality. -/
@[stacks 053A "Lemma 15.25.1"]
theorem ofFlatPrimeLocalizations
    {R : Type u} [CommRing R] (n : ℕ)
    {M : Type w} [AddCommGroup M] [Module (MvPolynomial (Fin n) R) M] [Module R M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M]
    (hdetect : PrimeLocalization.DetectsEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Module.FinitePresentation
          ((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R)
          (((Localization.AtPrime p.asIdeal) ⊗[R] MvPolynomial (Fin n) R) ⊗[
            MvPolynomial (Fin n) R] M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := sorry

end Module.FinitePresentation

namespace Algebra.FinitePresentation

/-- Lemma 15.25.2: a flat finite-type algebra is finitely presented when all prime-local base
changes are finitely presented and a finite family of base-prime localizations detects equality. -/
@[stacks 053B "Lemma 15.25.2"]
theorem ofFlatPrimeLocalizations
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hdetect : PrimeLocalization.DetectsEquality R)
    (hloc :
      ∀ p : PrimeSpectrum R,
        Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S)) :
    Algebra.FinitePresentation R S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := f.toRingHom.toAlgebra
  letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : Module.Finite P S := Module.Finite.of_surjective (Algebra.linearMap P S) hf
  letI : Module.FinitePresentation P S := by
    apply Module.FinitePresentation.ofFlatPrimeLocalizations n hdetect
    intro p
    let A := Localization.AtPrime p.asIdeal
    let B := A ⊗[R] P
    let C := B ⊗[P] S
    -- Identify the iterated base change with the prime-localized algebra.
    let eRing : C ≃+* A ⊗[R] S :=
      (Algebra.TensorProduct.comm P B S).toRingEquiv |>.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[P] S)
          (Algebra.TensorProduct.commRight R P A).symm).toRingEquiv |>.trans
        (Algebra.TensorProduct.cancelBaseChange R P P S A).toRingEquiv |>.trans
        (Algebra.TensorProduct.comm R S A).toRingEquiv
    let e : C ≃ₐ[A] A ⊗[R] S :=
      { eRing with
        commutes' := by
          intro a
          change (Algebra.TensorProduct.comm R S A)
            ((Algebra.TensorProduct.cancelBaseChange R P P S A)
              ((1 : S) ⊗ₜ[P] ((1 : P) ⊗ₜ[R] a))) = a ⊗ₜ[R] (1 : S)
          rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul,
            Algebra.TensorProduct.comm_tmul] }
    letI : Algebra.FinitePresentation A (A ⊗[R] S) := hloc p
    letI : Algebra.FinitePresentation A C := Algebra.FinitePresentation.equiv e.symm
    letI : Algebra.FinitePresentation B C :=
      Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C
    exact Module.FinitePresentation.of_finite_of_finitePresentation B C
  exact Algebra.FinitePresentation.of_surjective hf
    (Module.FinitePresentation.fg_ker (Algebra.linearMap P S) hf)

end Algebra.FinitePresentation
