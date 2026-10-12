/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.AtPrime
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded

@[expose] public section

/-!
# Principal-Quotient Criterion for Analytic Unramifiedness

This leaf records the associated-prime criterion that detects analytic
unramifiedness from a nonzero principal quotient of a Noetherian local domain.
-/

universe u

open IsLocalRing

namespace IsAnalyticallyUnramified

/-- Lemma 10.162.12, tag `0330`: a Noetherian local domain is analytically
unramified when a nonzero element of its maximal ideal has a principal quotient
without embedded associated primes and every associated-prime localization of
that quotient is regular and analytically unramified. -/
@[stacks 0330]
theorem of_principalQuotient_associatedPrimes {R : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (h_no_embedded :
      embeddedAssociatedPrimes R (R ⧸ Ideal.span ({x} : Set R)) = ∅)
    (h_regular :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal (R ⧸ Ideal.span ({x} : Set R)) →
          IsRegularLocalRing (Localization.AtPrime p.asIdeal))
    (h_analytic :
      ∀ p : PrimeSpectrum R,
        IsAssociatedPrime p.asIdeal (R ⧸ Ideal.span ({x} : Set R)) →
          PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsAnalyticallyUnramified R := sorry

end IsAnalyticallyUnramified
