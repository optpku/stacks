/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata.Localization
public import ReasLib.RingTheory.Normal.Nagata.Normal

@[expose] public section

/-!
# Local N-1 Criteria

This leaf records principal-open and maximal-local criteria for the `N-1`
condition on domains.
-/

universe u

namespace IsN1Ring

/-- Lemma 10.161.15 (1), tag `0333`: an `N-1` domain has a nonzero
principal-open localization that is normal. -/
@[stacks 0333 "(1)"]
theorem exists_normal_localizationAway {R : Type u} [CommRing R] [IsDomain R]
    [IsN1Ring R] :
    ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f) := sorry

/-- Lemma 10.161.15 (2), tag `0333`: an `N-1` domain remains `N-1` after
localization at a maximal ideal. -/
@[stacks 0333 "(2)"]
theorem atMaximal {R : Type u} [CommRing R] [IsDomain R] [IsN1Ring R]
    (m : MaximalSpectrum R) :
    IsN1Ring (Localization.AtPrime m.asIdeal) := sorry

/-- Lemma 10.161.15 (3), tag `0333`: a Noetherian domain is `N-1` when it is
normal on one nonzero principal open and `N-1` at every maximal localization. -/
@[stacks 0333 "(3)"]
theorem of_normal_localizationAway_of_forall_atMaximal
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h_normal : ∃ f : R, f ≠ 0 ∧ IsNormalRing (Localization.Away f))
    (h_local : ∀ m : MaximalSpectrum R, IsN1Ring (Localization.AtPrime m.asIdeal)) :
    IsN1Ring R := sorry

end IsN1Ring
