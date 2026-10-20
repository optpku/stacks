/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair

/-!
# Valuation-theoretic properties of fraction-subring pairs

This leaf adds valuation hypotheses to `FractionRing.SubringPair`.  The core
intersection and tensor comparison map remain in the smaller ring-theoretic
leaf, so consumers without valuation arguments do not import this material.
-/

@[expose] public section

universe u

namespace FractionRing.SubringPair

variable {K : Type u} [Field K]

/-- A fraction-subring pair is dominated by a discrete valuation subring of
the ambient field. -/
@[stacks 09N0 "dominating discrete valuation subring"]
def HasDominatingDVR (P : FractionRing.SubringPair K) : Prop :=
  ∃ V : ValuationSubring K,
    P.left ≤ V.toSubring ∧ P.right ≤ V.toSubring ∧ IsDiscreteValuationRing V

/-- Unfold `HasDominatingDVR` into a valuation subring containing both
components. -/
@[stacks 09N0 "dominating discrete valuation subring criterion"]
theorem hasDominatingDVR_iff (P : FractionRing.SubringPair K) :
    P.HasDominatingDVR ↔
      ∃ V : ValuationSubring K,
        P.left ≤ V.toSubring ∧ P.right ≤ V.toSubring ∧ IsDiscreteValuationRing V := sorry

/-- If the right component is a valuation ring, a unit of the left component
or its inverse belongs to the intersection. -/
@[stacks 09MZ "unit or inverse in fraction-ring intersection"]
theorem unit_mem_intersection_or_inv_mem_intersection
    (P : FractionRing.SubringPair K) [ValuationRing P.right] (u : P.leftˣ) :
    ((u : P.left) : K) ∈ P.intersection ∨
      (((u⁻¹ : P.leftˣ) : P.left) : K) ∈ P.intersection := sorry

/-- For a Noetherian left component of Krull dimension one, the tensor
comparison to the ambient field is nonsurjective exactly when the pair has a
dominating discrete valuation subring. -/
@[stacks 09N0]
theorem tensorToAmbient_not_surjective_iff_hasDominatingDVR
    (P : FractionRing.SubringPair K) [IsNoetherianRing P.left]
    (hdim : ringKrullDim P.left = 1) :
    ¬ Function.Surjective P.tensorToAmbient ↔ P.HasDominatingDVR := sorry

end FractionRing.SubringPair
