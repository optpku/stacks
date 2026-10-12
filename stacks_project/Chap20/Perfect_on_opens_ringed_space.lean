/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Local
import StacksCheckRecall

@[expose] public section

/- Perfectness is detected by strictly perfect representatives on an open cover. -/
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isPerfect_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect.ModelOn

