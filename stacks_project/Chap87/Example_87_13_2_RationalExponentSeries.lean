module

public import ReasLib.RingTheory.Valuation.RationalExponentSeries
import StacksCheckRecall

universe u

/- Example 87.13.2: Rational-exponent series have finite support in every bounded interval. -/
@[stacks 0CB8] #check (RationalExponentSeries :
  ∀ (κ : Type u) [CommRing κ], Subring (HahnSeries ℚ≥0 κ))
