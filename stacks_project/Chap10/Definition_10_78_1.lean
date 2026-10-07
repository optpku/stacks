module

public import ReasLib.RingTheory.Flatness.LocallyFree
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.78.1

@stack 00NW

This chapter entry is a source-facing recall of the reusable finite-locally-free
module API in `ReasLib.RingTheory.Flatness.LocallyFree`.
-/

/- Definition 10.78.1: `Module.LocallyFree`, `Module.FiniteLocallyFree`, and
`Module.FiniteLocallyFreeOfRank` are the neutral owners for the three local freeness conditions. -/
@[stacks 00NW "locally free module"]
#check @Module.LocallyFree
@[stacks 00NW "finite locally free module"]
#check @Module.FiniteLocallyFree
@[stacks 00NW "finite locally free module of fixed rank"]
#check @Module.FiniteLocallyFreeOfRank

/- The reusable rank bridge API. -/
@[stacks 00NW "forget fixed rank"]
#check @Module.FiniteLocallyFreeOfRank.finiteLocallyFree
