/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Flat
import StacksCheckRecall

@[expose] public section

/- Definition 17.17.1 (05ND): flat module sheaves on a ringed space. -/
@[stacks 05ND]
#check @SheafOfModules.IsFlat

#check @SheafOfModules.IsFlat.iff_forall_isFlatAt

#check @SheafOfModules.IsLocallyFree.isFlat
