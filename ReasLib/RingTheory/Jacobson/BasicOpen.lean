/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import ReasLib.RingTheory.Spectrum.Prime.Localization.Away
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic-open charts in Jacobson spectra

This leaf relates the Jacobson property to locally closed basic-open charts in the prime
spectrum. The chart, field, and infinitude conclusions are separate so downstream arguments can
reuse them without unpacking a source-specific conjunction.

@stack 034J
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R]

/-- A non-Jacobson ring has a nonmaximal prime isolated by a basic open inside its closure. -/
@[stacks 034J "non-Jacobson singleton chart"]
theorem exists_nonmaximal_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing
    (hR : ¬ IsJacobsonRing R) :
    ∃ (p : PrimeSpectrum R) (f : R),
      ¬ p.asIdeal.IsMaximal ∧
        zeroLocus (p.asIdeal : Set R) ∩
          (basicOpen f : Set (PrimeSpectrum R)) = {p} := sorry

/-- A singleton basic-open chart in the closure of a prime presents a field after quotienting by
the prime and localizing at the chart function. -/
@[stacks 034J "singleton chart is a field"]
theorem isField_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton
    (p : PrimeSpectrum R) (f : R)
    (hp : zeroLocus (p.asIdeal : Set R) ∩
      (basicOpen f : Set (PrimeSpectrum R)) = {p}) :
    IsField (Localization.Away (Ideal.Quotient.mk p.asIdeal f)) := sorry

/-- In a Jacobson spectrum, every basic-open chart in the closure of a nonmaximal prime is
infinite. -/
@[stacks 034J "Jacobson charts are infinite"]
theorem infinite_zeroLocus_inter_basicOpen_of_isJacobsonRing
    [IsJacobsonRing R] (p : PrimeSpectrum R) (f : R)
    (hp : ¬ p.asIdeal.IsMaximal) (hf : f ∉ p.asIdeal) :
    Set.Infinite
      (zeroLocus (p.asIdeal : Set R) ∩
        (basicOpen f : Set (PrimeSpectrum R))) := sorry

end PrimeSpectrum
