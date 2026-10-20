/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

universe u

namespace ValuationRing

/-- There exists a valuation ring with a prime ideal distinct from both the zero
ideal and the maximal ideal. -/
theorem exists_intermediatePrime :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : ValuationRing A)
      (p : Ideal A) (_ : p.IsPrime),
      p ≠ ⊥ ∧ p ≠ IsLocalRing.maximalIdeal A := sorry

end ValuationRing
