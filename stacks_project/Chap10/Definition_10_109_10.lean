module

public import ReasLib.RingTheory.GlobalDimension.Basic
import StacksCheckRecall

/-!
# Definition 10.109.10

@stack 00O6
-/

@[expose] public section

/- Definition 10.109.10 [stacks 00O6]: a ring has finite global dimension when there is a
uniform natural-number bound on the projective dimensions of all its modules. The canonical
owner records the bound in the ring-sized module category and supplies the same bound in every
module universe through `HasGlobalDimensionLE.hasProjectiveDimensionLE_of_module`. The least
such bound is `globalDimension R`. -/
@[stacks 00O6]
#check @IsFiniteGlobalDimensionRing

@[stacks 00O6 "uniform projective-dimension bound"]
#check @HasGlobalDimensionLE

@[stacks 00O6 "module-category transfer"]
#check @HasGlobalDimensionLE.hasProjectiveDimensionLE_of_module

@[stacks 00O6 "global dimension invariant"]
#check @globalDimension

@[stacks 00O6 "global dimension realizes a bound"]
#check @hasGlobalDimensionLE_globalDimension

@[stacks 00O6 "global dimension is minimal"]
#check @globalDimension_le
