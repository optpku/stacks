/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Noetherian Valuation Rings

@stack 00II

This leaf records the Noetherian dichotomy for a valuation domain.  The result
is a theorem, not an instance: the disjunction is a derived classification and
must not influence typeclass search.
-/

@[expose] public section

universe u

namespace ValuationRing

/-- Lemma 10.50.18 (Tag 00II): a valuation domain is Noetherian exactly when it is a discrete
valuation ring or a field. -/
@[stacks 00II]
theorem isNoetherianRing_iff_isDiscreteValuationRing_or_isField
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    IsNoetherianRing A ↔ IsDiscreteValuationRing A ∨ IsField A := sorry

end ValuationRing
