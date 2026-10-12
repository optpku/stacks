/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Characterizations of Valuation Rings

@stack 052K
@stack 090Q

This leaf contains source-facing bridges for the canonical `ValuationRing`
owner.  The primary criterion remains mathlib's `IsBezout` formulation; the
finitely-generated-ideal formulation is exposed only as a thin reusable view.
-/

@[expose] public section

universe u

namespace ValuationRing

/-- Lemma 10.50.15: for a commutative domain, being a valuation ring is equivalent to being local
and having every finitely generated ideal principal. -/
@[stacks 090Q]
theorem iff_local_and_fg_ideals_principal
    (A : Type u) [CommRing A] [IsDomain A] :
    ValuationRing A ↔ IsLocalRing A ∧ ∀ I : Ideal A, I.FG → I.IsPrincipal := sorry

end ValuationRing

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
