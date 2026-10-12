/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Analytically ramified local domains

This module records existence results for Noetherian local domains whose
maximal-ideal adic completions or principal-adic completions after localization
are not reduced.
-/

universe u

namespace IsAnalyticallyUnramified

/-- There exists a characteristic-zero, one-dimensional Noetherian local domain which is not
analytically unramified. -/
@[stacks 00PC "characteristic-zero analytically ramified local domain"]
theorem exists_charZero_localDomain_counterexample :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A) (_ : CharZero A),
      ringKrullDim A = 1 ∧ ¬ IsAnalyticallyUnramified A := sorry

/-- There exists a Noetherian local domain whose maximal-ideal adic completion is not reduced. -/
@[stacks 039U]
theorem exists_noetherianLocalDomain_with_nonreduced_completion :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsNoetherianRing A)
      (_ : IsLocalRing A),
      ¬ IsReduced (AdicCompletion (IsLocalRing.maximalIdeal A) A) := sorry

end IsAnalyticallyUnramified

namespace AdicCompletion.Counterexample

/-- There exists a two-dimensional Noetherian local domain complete along a principal ideal,
with an element of the maximal ideal outside that ideal, such that completing after inverting
that element is nonreduced and remains nonreduced after inverting the principal generator. -/
theorem exists_nonreduced_localization :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B) (b f : B),
      ringKrullDim B = 2 ∧ IsAdicComplete (Ideal.span {b}) B ∧
        f ∈ IsLocalRing.maximalIdeal B ∧ f ∉ Ideal.span {b} ∧
        ¬ IsReduced
          (AdicCompletion (Ideal.map (algebraMap B (Localization.Away f)) (Ideal.span {b}))
            (Localization.Away f)) ∧
        ¬ IsReduced
          (Localization.Away
            (algebraMap B
              (AdicCompletion (Ideal.map (algebraMap B (Localization.Away f)) (Ideal.span {b}))
                (Localization.Away f)) b)) := sorry

end AdicCompletion.Counterexample
