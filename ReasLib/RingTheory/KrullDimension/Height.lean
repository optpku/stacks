/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Krull dimension as a supremum of ideal heights

Mathlib computes Krull dimension from prime and maximal-ideal heights under a
`Nontrivial` assumption.  This leaf gives the corresponding `WithBot` formulas
for every commutative ring; in the subsingleton case both sides are bottom.
-/

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The Krull dimension of a commutative ring is the supremum, in
`WithBot ℕ∞`, of the heights of its maximal ideals. -/
@[stacks 00KG "maximal-ideal height supremum"]
theorem iSup_isMaximal_height_eq_ringKrullDim :
    (⨆ (I : Ideal R) (_ : I.IsMaximal), (I.height : WithBot ℕ∞)) =
      ringKrullDim R := sorry

/-- The Krull dimension of a commutative ring is the supremum, in
`WithBot ℕ∞`, of the heights of its prime ideals. -/
@[stacks 00KG "prime-ideal height supremum"]
theorem iSup_isPrime_height_eq_ringKrullDim :
    (⨆ (I : Ideal R) (_ : I.IsPrime), (I.height : WithBot ℕ∞)) =
      ringKrullDim R := sorry

end Ideal
