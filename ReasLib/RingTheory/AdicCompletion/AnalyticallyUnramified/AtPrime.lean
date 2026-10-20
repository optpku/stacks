/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified

@[expose] public section

/-!
# Associated Primes in Analytically Unramified Completions

This leaf records reducedness of completed prime quotients and the induced
discrete-valuation-ring statement at their associated primes.
-/

universe u

open IsLocalRing

namespace PrimeSpectrum.IsAnalyticallyUnramified

/-- An analytically unramified prime quotient of a Noetherian local ring gives
a reduced corresponding quotient of the maximal-ideal completion. -/
@[stacks 032Z "reduced completed quotient"]
theorem completionQuotient_isReduced {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : PrimeSpectrum R) (h_analytic : PrimeSpectrum.IsAnalyticallyUnramified p) :
    IsReduced
      (AdicCompletion (maximalIdeal R) R ⧸
        Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) p.asIdeal) := sorry

/-- Lemma 10.162.11, tag `032Z`: let `p` be an analytically unramified prime
of a Noetherian local ring.  If `R_p` is a discrete valuation ring, then the
localization at every associated prime of the completed quotient
`R^∧ ⧸ pR^∧` is a discrete valuation ring. -/
@[stacks 032Z]
theorem exists_discreteValuationRing_of_completionAssociatedPrime {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : PrimeSpectrum R) (q : PrimeSpectrum (AdicCompletion (maximalIdeal R) R))
    (h_dvr :
      ∃ (_ : IsDomain (Localization.AtPrime p.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime p.asIdeal))
    (h_analytic : PrimeSpectrum.IsAnalyticallyUnramified p)
    (hq :
      IsAssociatedPrime q.asIdeal
        (AdicCompletion (maximalIdeal R) R ⧸
          Ideal.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) p.asIdeal)) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := sorry

end PrimeSpectrum.IsAnalyticallyUnramified
