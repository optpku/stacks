module

public import ReasLib.RingTheory.Valuation.DirectLimit
import StacksCheckRecall

/-!
# Directed colimits of valuation rings

@stack 0AS4
-/

@[expose] public section

/- Lemma 10.50.6 (Tag 0AS4): canonical recall of the reusable directed-colimit
valuation-ring API.  The independent domain and pre-valuation-ring components
remain available separately, with total divisibility supplied by mathlib's
`PreValuationRing.iff_dvd_total`. -/
@[stacks 0AS4 "direct-limit domain"]
#check @Ring.DirectLimit.isDomain

@[stacks 0AS4 "direct-limit pre-valuation ring"]
#check @Ring.DirectLimit.preValuationRing

@[stacks 0AS4 "total divisibility criterion"]
#check @PreValuationRing.iff_dvd_total

@[stacks 0AS4 "direct-limit valuation ring"]
#check @Ring.DirectLimit.valuationRing
