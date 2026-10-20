/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.Dimension
public import ReasLib.RingTheory.DiscreteValuationRing.Characterization
public import ReasLib.RingTheory.RegularLocalRing.Completion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete Valuation Rings and Maximal-Ideal Completion

@stack 0AP1
-/

@[expose] public section

open IsLocalRing

universe u

namespace AdicCompletion

/-- Lemma 15.43.5 (0AP1): a Noetherian local ring is a discrete valuation ring exactly when its
maximal-ideal adic completion is a discrete valuation ring. -/
@[stacks 0AP1 "DVR property and maximal-ideal completion"]
theorem isDiscreteValuationRing_iff
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    (exists _ : IsDomain A, IsDiscreteValuationRing A) ↔
      exists _ : IsDomain (AdicCompletion (maximalIdeal A) A),
        IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
