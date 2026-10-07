module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Coherent.Basic

@[expose] public section

/-!
# Valuation Rings Are Coherent

@stack 0EWV

The coherent-ring instance attached to a valuation ring.
-/

universe u

/-- Example 10.90.2: every valuation ring is coherent. -/
@[stacks 0EWV]
instance valuationRing_isCoherentRing (A : Type u) [CommRing A] [IsDomain A]
    [ValuationRing A] : IsCoherentRing A := sorry
