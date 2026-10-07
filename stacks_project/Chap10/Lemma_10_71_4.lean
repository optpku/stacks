module

public import ReasLib.Algebra.Homology.ChainComplex.FreeResolution.Comparison
import StacksCheckRecall

/-!
# Lifting maps to resolutions

@stack 00LS
-/

@[expose] public section

@[stacks 00LS "(1), lift to a resolution"]
#check @ChainComplex.IsTermwiseFree.exists_lift_to_resolution

@[stacks 00LS "(2), uniqueness up to homotopy"]
#check @ChainComplex.IsTermwiseFree.homotopic_lifts_to_resolution
