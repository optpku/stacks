module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Coherent.Basic

@[expose] public section

/-!
# Valuation Rings Are Coherent

Every valuation domain is a coherent ring.
-/

universe u

/-- Every valuation domain is coherent. -/
@[stacks 0EWV]
instance valuationRing_isCoherentRing (A : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] : IsCoherentRing A := sorry
