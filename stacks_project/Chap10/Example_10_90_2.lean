module

public import ReasLib.RingTheory.Coherent.Valuation
import StacksCheckRecall

@[expose] public section

/-!
# Example 10.90.2

@stack 0EWV

Valuation rings carry the canonical coherent-ring instance.
-/

@[stacks 0EWV "coherent-ring owner"]
#check @IsCoherentRing

@[stacks 0EWV "valuation-ring criterion"]
#check @ValuationRing.iff_local_bezout_domain

@[stacks 0EWV "valuation rings are coherent"]
#check @valuationRing_isCoherentRing
