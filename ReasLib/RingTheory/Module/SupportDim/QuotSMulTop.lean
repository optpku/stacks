/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Support dimension after a principal module quotient

The ambient support-dimension and regular-element inequalities are owned by Mathlib.  This leaf
packages the two source-facing bounds for a finite module over a Noetherian local ring, keeping
`QuotSMulTop` as the canonical quotient object.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- The second bound is already the canonical Mathlib theorem and deliberately keeps its
Noetherian/local finite-module assumptions. -/

/-- Lemma 10.63.10 (1) (Stacks `0B52`): the support dimension of a principal module quotient is
bounded by that of the original module.  This is the general quotient-map API underlying the
source-facing local statement. -/
@[stacks 0B52 "(1), general quotient form"]
theorem supportDim_quotSMulTop_le (f : R) :
    supportDim R (QuotSMulTop f M) ≤ supportDim R M := sorry
/- Proof strategy: apply the support-dimension monotonicity theorem for a
surjective quotient map, using the canonical map from `M` to `QuotSMulTop f M`. -/

end Module
