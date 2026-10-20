/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.LocalSubring
public import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal local-subring characterization

This leaf owns the valuation-ring characterization in terms of the canonical
local-subring order on the fraction field.  The carrier is the range of the
fraction-field map; callers do not need to rebuild a `LocalSubring` or choose a
valuation overring locally.

@stack 00I9
-/

@[expose] public section

universe u

namespace ValuationRing

/- Definition 10.50.1 (Tag 00I9): a local domain is a valuation ring exactly
when its image in its fraction field is maximal for the domination order. -/
@[stacks 00I9]
theorem iff_isMax_range_fractionRing
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] :
    ValuationRing A ↔
      IsMax (LocalSubring.range (algebraMap A (FractionRing A))) := sorry

end ValuationRing
