module

import StacksCheckRecall
public import ReasLib.RingTheory.WeakDimension

/-!
# Definition 15.105.3

@stack 092D
-/

@[expose] public section

/- Definition 15.105.3, tag `092D`: a ring has weak dimension at most `d` when every module has
Tor dimension at most `d`. -/
@[stacks 092D]
#check @HasWeakDimensionLE

/- The reusable module-level consequence of a weak-dimension bound. -/
#check @HasWeakDimensionLE.hasTorDimensionLE
