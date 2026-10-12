/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.CompleteLocal

@[expose] public section

/-!
# Local Complete Intersection Rings

This module defines complete-intersection local rings through their completions and local complete
intersection rings through their prime localizations.
-/

universe u

open IsLocalRing

section

variable {R : Type u} [CommRing R]

/-- Definition 23.8.5 (1): a Noetherian local ring is a complete intersection when its
maximal-ideal adic completion is a complete-intersection complete local ring. -/
@[stacks 09Q3 "(1)"]
class IsCompleteIntersectionLocalRing (R : Type u) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  /-- The maximal-ideal completion is a complete-intersection complete local ring. -/
  completion_isCompleteIntersection :
    IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R)

/-- The complete-intersection local condition as a Noetherian condition and a completion
condition. -/
@[stacks 09Q3 "local complete-intersection completion criterion"]
theorem isCompleteIntersectionLocalRing_iff (R : Type u) [CommRing R] [IsLocalRing R] :
    IsCompleteIntersectionLocalRing R ↔
      IsNoetherianRing R ∧
        IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R) := sorry

attribute [instance] IsCompleteIntersectionLocalRing.completion_isCompleteIntersection

namespace IsCompleteIntersectionLocalRing

/-- Build a complete-intersection local ring from its complete-intersection completion. -/
@[stacks 09Q3 "local complete-intersection completion constructor"]
theorem of_completion
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hCompletion :
      IsCompleteIntersectionCompleteLocalRing (AdicCompletion (maximalIdeal R) R)) :
    IsCompleteIntersectionLocalRing R := sorry

/-- For an already complete Noetherian local ring, the local and complete-local
complete-intersection predicates agree. -/
@[stacks 09Q3 "complete-local comparison"]
theorem iff_complete
    (R : Type u) [CommRing R] [IsCompleteLocalRing R] [IsNoetherianRing R] :
    IsCompleteIntersectionLocalRing R ↔ IsCompleteIntersectionCompleteLocalRing R := sorry

end IsCompleteIntersectionLocalRing

/-- Definition 23.8.5 (2): a Noetherian ring is a local complete intersection when all of its
prime localizations are complete-intersection local rings. -/
@[stacks 09Q3 "(2)"]
class IsLocalCompleteIntersectionRing (R : Type u) [CommRing R] : Prop extends
    IsNoetherianRing R where
  /-- The complete-intersection condition at every prime localization. -/
  completeIntersection_atPrime :
    ∀ p : PrimeSpectrum R, IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal)

/-- The local-complete-intersection condition as a Noetherian condition and a primewise local
criterion. -/
@[stacks 09Q3 "local complete-intersection primewise criterion"]
theorem isLocalCompleteIntersectionRing_iff (R : Type u) [CommRing R] :
    IsLocalCompleteIntersectionRing R ↔
      IsNoetherianRing R ∧
        ∀ p : PrimeSpectrum R,
          IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal) := sorry

attribute [instance] IsLocalCompleteIntersectionRing.completeIntersection_atPrime

namespace IsLocalCompleteIntersectionRing

/-- Build a local complete intersection ring from its primewise complete-intersection local
conditions. -/
@[stacks 09Q3 "primewise local complete-intersection constructor"]
theorem of_localizationAtPrime
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hPrime :
      ∀ p : PrimeSpectrum R, IsCompleteIntersectionLocalRing (Localization.AtPrime p.asIdeal)) :
    IsLocalCompleteIntersectionRing R := sorry

end IsLocalCompleteIntersectionRing

end
