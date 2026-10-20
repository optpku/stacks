module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Regular local rings from Serre's condition `(R_k)`

This file provides the local-ring bridge used when passing between ring-level and scheme-level
forms of Serre's regularity condition.
-/

@[expose] public section

universe u

namespace SerreConditionR

/-- A local ring satisfying `(R_k)` is regular when its Krull dimension is at most `k`. -/
theorem isRegularLocalRing_of_ringKrullDim_le
    (A : Type u) [CommRing A] [IsLocalRing A] {k : ℕ} [SerreConditionR A k]
    (hk : ringKrullDim A ≤ k) :
    IsRegularLocalRing A := by
  have hheight : (IsLocalRing.maximalIdeal A).height ≤ k := by
    have h := hk
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h
    exact_mod_cast h
  have hreg : IsRegularLocalRing
      (Localization.AtPrime (IsLocalRing.maximalIdeal A)) :=
    SerreConditionR.isRegularLocalRing_localizationAtPrime
      (IsLocalRing.closedPoint A) hheight
  -- Local instance justification (proof-local temporary data): install this result temporarily for transport across the localization equivalence.
  letI := hreg
  let e : A ≃ₐ[A] Localization.AtPrime (IsLocalRing.maximalIdeal A) :=
    IsLocalization.atUnits A (IsLocalRing.maximalIdeal A).primeCompl
      (fun x ↦ by simpa using! fun a ↦ a)
  exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm

end SerreConditionR
