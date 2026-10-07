module

import StacksCheckRecall
public import ReasLib.RingTheory.AbsolutelyIntegrallyClosed

@[expose] public section

/- Definition 15.14.1: a ring is absolutely integrally closed when every monic
polynomial splits into linear factors. -/
/-!
@stack 0DCL
-/
@[stacks 0DCL "Definition 15.14.1"]
#check @IsAbsolutelyIntegrallyClosed

/- The defining splitting operation is exposed directly by the reusable owner. -/
#check @IsAbsolutelyIntegrallyClosed.splits
