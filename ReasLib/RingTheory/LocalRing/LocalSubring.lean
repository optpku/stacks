/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.LocalSubring

@[expose] public section

universe u

namespace LocalSubring

/-- One local subring dominates another exactly when it contains that subring and its
maximal ideal contracts to the maximal ideal of the smaller subring. -/
theorem le_iff_maximalIdeal_comap {R : Type u} [CommRing R] (A B : LocalSubring R) :
    A ≤ B ↔ ∃ h : A.toSubring ≤ B.toSubring,
      (IsLocalRing.maximalIdeal B.toSubring).comap (Subring.inclusion h) =
        IsLocalRing.maximalIdeal A.toSubring := sorry

end LocalSubring
