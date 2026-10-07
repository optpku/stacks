module

public import ReasLib.RingTheory.Localization.FractionRing.OneDimensionalOverring
import StacksCheckRecall

/-!
# A One-Dimensional Local Overring

The canonical owner returns the local, one-dimensional, essentially
finite-type overring; Noetherianity is a standard consequence.

@stack 00P8
-/

@[expose] public section

@[stacks 00P8 "one-dimensional local overring"]
#check @FractionRing.exists_local_dimOne_overring_of_not_isField
