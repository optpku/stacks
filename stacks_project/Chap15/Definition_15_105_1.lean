module

import StacksCheckRecall
public import ReasLib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.AbsolutelyFlat

/-!
# Definition 15.105.1

@stack 092B
-/

@[expose] public section

/- Definition 15.105.1 (1), tag `092B`: an absolutely flat ring is a ring over which every
module is flat.  The shared owner uses the equivalent universe-independent element criterion. -/
@[stacks 092B "absolutely flat rings"]
#check @IsAbsolutelyFlatRing

/- Definition 15.105.1 (1), canonical characterization by flatness of all modules. -/
#check @IsAbsolutelyFlatRing.iff_forall_module_flat

/- Definition 15.105.1 (2), tag `092B`: a weakly etale algebra has flat structure and
tensor-square multiplication maps. -/
@[stacks 092B "weakly etale ring maps"]
#check @Algebra.WeaklyEtale
