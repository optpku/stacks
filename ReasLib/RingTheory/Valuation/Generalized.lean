/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Generalized valuation rings

This leaf keeps the three source formulations together while using Mathlib's
`PreValuationRing` as the reusable owner of the divisibility condition.

@stack 0ASN
-/

@[expose] public section

universe u

namespace ValuationRing

/-- Lemma 15.125.2 (Generalized valuation rings) (0ASN): for a nonzero commutative ring, total divisibility,
being local Bézout, and total ordering of ideals are equivalent. -/
@[stacks 0ASN "generalized valuation ring TFAE"]
theorem generalizedValuationRing_tfae
    (R : Type u) [CommRing R] [Nontrivial R] :
    List.TFAE
      [@Std.Total R (· ∣ ·),
        IsLocalRing R ∧ IsBezout R,
        @Std.Total (Ideal R) (· ≤ ·)] := sorry
-- Proof strategy: use `PreValuationRing.iff_dvd_total` for the elementwise
-- formulation.  Total divisibility makes `R` local and every finitely generated
-- ideal principal.  In a local Bezout ring, a generator of `(a, b)` forces one
-- coefficient to be a unit, so principal ideals, and then arbitrary ideals,
-- are comparable.  Comparability of all ideals specializes back to principal
-- ideals and hence to total divisibility.

end ValuationRing
