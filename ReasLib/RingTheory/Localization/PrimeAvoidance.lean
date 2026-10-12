/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.RingTheory.LocalProperties.Semilocal
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# Localization away from finitely many prime ideals

This leaf packages the multiplicative submonoid obtained by avoiding every
member of a finite family of prime ideals, along with the resulting semilocal
localization and its maximal-ideal correspondence.
-/

@[expose] public section

universe u

namespace PrimeSpectrum.Avoidance

variable {A : Type u} [CommRing A]

/-- The multiplicative submonoid of elements avoiding every prime in `s`. -/
def submonoid (s : Finset (PrimeSpectrum A)) : Submonoid A :=
  ⨅ p : s, p.1.asIdeal.primeCompl

/-- Membership in the finite-prime avoidance submonoid means avoiding each selected prime. -/
theorem mem_submonoid_iff (s : Finset (PrimeSpectrum A)) (a : A) :
    a ∈ submonoid s ↔ ∀ p ∈ s, a ∉ p.asIdeal := sorry

/-- Localizing away from a finite family of prime ideals produces a semilocal ring. -/
instance instFiniteMaximalSpectrumLocalization
    (s : Finset (PrimeSpectrum A)) :
    Finite (MaximalSpectrum (Localization (submonoid s))) := sorry

/-- The contraction of a maximal ideal after finite-prime avoidance localization is maximal
among the selected prime ideals. -/
theorem comap_maximal
    (s : Finset (PrimeSpectrum A))
    (J : Ideal (Localization (submonoid s))) (hJ : J.IsMaximal) :
    Maximal (· ∈ (s.image PrimeSpectrum.asIdeal : Set (Ideal A)))
      (Ideal.comap (algebraMap A (Localization (submonoid s))) J) := sorry

/-- A prime ideal maximal among the selected family extends to a maximal ideal after finite-prime
avoidance localization and contracts back to itself. -/
theorem map_maximal
    (s : Finset (PrimeSpectrum A))
    (p : Ideal A) (hp : Maximal (· ∈ (s.image PrimeSpectrum.asIdeal : Set (Ideal A))) p) :
    (Ideal.map (algebraMap A (Localization (submonoid s))) p).IsMaximal ∧
      Ideal.comap (algebraMap A (Localization (submonoid s)))
        (Ideal.map (algebraMap A (Localization (submonoid s))) p) = p := sorry

/-- Contract a maximal ideal of the finite-prime avoidance localization to an
inclusion-maximal member of the selected family. -/
def maximalIdealComap (s : Finset (PrimeSpectrum A)) :
    MaximalSpectrum (Localization (submonoid s)) →
      {p : Ideal A // Maximal (· ∈ (s.image PrimeSpectrum.asIdeal : Set (Ideal A))) p} :=
  fun J ↦ ⟨Ideal.comap (algebraMap A (Localization (submonoid s))) J.asIdeal,
    comap_maximal s J.asIdeal J.isMaximal⟩

/-- Extend an inclusion-maximal member of a selected finite family of prime ideals to a
maximal ideal of the finite-prime avoidance localization. -/
def maximalIdealMap (s : Finset (PrimeSpectrum A)) :
    {p : Ideal A // Maximal (· ∈ (s.image PrimeSpectrum.asIdeal : Set (Ideal A))) p} →
      MaximalSpectrum (Localization (submonoid s)) :=
  fun p ↦ ⟨Ideal.map (algebraMap A (Localization (submonoid s))) p.1,
    (map_maximal s p.1 p.2).1⟩

/-- Extending the contraction of a maximal ideal of the localization recovers that ideal. -/
theorem maximalIdealMap_comap (s : Finset (PrimeSpectrum A))
    (J : MaximalSpectrum (Localization (submonoid s))) :
    maximalIdealMap s (maximalIdealComap s J) = J := sorry

/-- Contracting the extension of an inclusion-maximal selected prime ideal recovers that
ideal. -/
theorem maximalIdealComap_map (s : Finset (PrimeSpectrum A))
    (p : {p : Ideal A // Maximal (· ∈ (s.image PrimeSpectrum.asIdeal : Set (Ideal A))) p}) :
    maximalIdealComap s (maximalIdealMap s p) = p := sorry

/-- Maximal ideals of the finite-prime avoidance localization correspond to the
inclusion-maximal prime ideals in the selected family. -/
def maximalSpectrumEquiv (s : Finset (PrimeSpectrum A)) :
    MaximalSpectrum (Localization (submonoid s)) ≃
      {p : Ideal A // Maximal (· ∈ (s.image PrimeSpectrum.asIdeal : Set (Ideal A))) p} where
  toFun := maximalIdealComap s
  invFun := maximalIdealMap s
  left_inv := maximalIdealMap_comap s
  right_inv := maximalIdealComap_map s

/-- A localization away from finitely many prime ideals has finite maximal spectrum, and
contraction bijects its maximal ideals with the inclusion-maximal selected prime ideals. -/
theorem finiteMaximalSpectrum_and_bijective_comap (s : Finset (PrimeSpectrum A)) :
    Finite (MaximalSpectrum (Localization (submonoid s))) ∧
      Function.Bijective (maximalIdealComap s) := sorry

end PrimeSpectrum.Avoidance
