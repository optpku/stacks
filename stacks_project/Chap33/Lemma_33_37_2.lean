module

import StacksCheckRecall
public import ReasLib.RingTheory.Localization.FractionRing.SubringPair.Valuation

@[expose] public section

universe u

/- Lemma 33.37.2 (Tag 09MZ) is the valuation-ring dichotomy for a unit of one
component of a `FractionRing.SubringPair`.  The shared owner is deliberately
stated for arbitrary pairs with a common fraction field.
-/
@[stacks 09MZ] #check
  (FractionRing.SubringPair.unit_mem_intersection_or_inv_mem_intersection :
    ∀ {K : Type u} [Field K] (P : FractionRing.SubringPair K) [ValuationRing P.right]
      (u : P.leftˣ),
      ((u : P.left) : K) ∈ P.intersection ∨
        (((u⁻¹ : P.leftˣ) : P.left) : K) ∈ P.intersection)
