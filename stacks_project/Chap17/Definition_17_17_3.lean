/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
import StacksCheckRecall

@[expose] public section

/- Definition 17.17.3 (05NF): flatness of a module sheaf at a point. -/
@[stacks 05NF]
#check @SheafOfModules.IsFlatAt
