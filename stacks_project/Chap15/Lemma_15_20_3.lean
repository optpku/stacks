module

public import ReasLib.RingTheory.Ideal.FlatQuotient.ClosedFiber
import StacksCheckRecall

/-!
# Finite-type local base-change criterion

Lemma 15.20.3 removes the Noetherian assumption on the local target when the source algebra is
finite type.

@stack 0528
-/

@[stacks 0528 "Lemma 15.20.3"]
#check @Ideal.IsClosedFiberFlatQuotient.baseChange_iff_map_eq_bot_of_finiteType

@[stacks 0528 "closed-fiber flat quotient ideal"]
#check @Ideal.IsClosedFiberFlatQuotient
