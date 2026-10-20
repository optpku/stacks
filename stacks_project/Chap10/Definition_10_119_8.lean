module

public import ReasLib.RingTheory.DiscreteValuationRing.Characterization
import StacksCheckRecall

/-!
# Uniformizers in Discrete Valuation Rings

@stack 09DZ
-/

@[expose] public section

/- Definition 10.119.8: an element of a discrete valuation ring is a uniformizer when it
generates the maximal ideal.  The canonical API records this condition as irreducibility. -/
@[stacks 09DZ]
#check @IsDiscreteValuationRing.maximalIdeal_eq_span_singleton_iff_irreducible

@[stacks 09DZ "uniformizer characterization"]
#check @IsDiscreteValuationRing.irreducible_iff_uniformizer

export IsDiscreteValuationRing (maximalIdeal_eq_span_singleton_iff_irreducible)
