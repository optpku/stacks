/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizations of Valuation Rings

@stack 052K

This leaf contains source-facing bridges for the canonical `ValuationRing`
owner.  The local Bezout-domain criterion is mathlib's
`ValuationRing.iff_local_bezout_domain`; `IsBezout.isPrincipal_of_FG` exposes
the finitely-generated-ideal condition.
-/

@[expose] public section

universe u

namespace Subring

variable {K : Type u} [Field K]

/-- Lemma 10.50.5 (1): a subring of a field containing either `x` or `x⁻¹` for every `x : K` is a
valuation ring. -/
@[stacks 052K "(1), valuation ring"]
theorem valuationRing_of_mem_or_inv_mem (A : Subring K)
    (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) :
    ValuationRing A := sorry

/-- Lemma 10.50.5 (2): under the same criterion, the ambient field is a fraction field of the
subring. -/
@[stacks 052K "(2), fraction field"]
theorem isFractionRing_of_mem_or_inv_mem (A : Subring K)
    (hA : ∀ x : K, x ∈ A ∨ x⁻¹ ∈ A) :
    IsFractionRing A K := sorry

end Subring
