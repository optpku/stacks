module

public import ReasLib.RingTheory.Valuation.Maximal
public import Mathlib.RingTheory.Valuation.LocalSubring
import StacksCheckRecall

/-!
@stack 00I9
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 10.50.1 is a canonical recall.  Domination is the order on
`LocalSubring`, and the source-facing maximality criterion is owned by the
shared valuation library. -/
@[stacks 00I9]
#check @LocalSubring.le_def

@[stacks 00I9]
#check @ValuationRing

@[stacks 00I9]
#check @LocalSubring.isMax_iff

/- Definition 10.50.1 (Tag 00I9): reusable maximality criterion. -/
@[stacks 00I9]
#check @ValuationRing.iff_isMax_range_fractionRing

section

variable {K : Type u} [Field K] (V : ValuationSubring K) (R : Subring K)

/- Definition 10.50.1: the Stacks phrase “`V` is centered on `R`” is exactly the containment
condition `R ≤ V.toSubring`. -/
@[stacks 00I9 "centered valuation subring"]
#check R ≤ V.toSubring

end
