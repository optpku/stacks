/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
import StacksCheckRecall

@[expose] public section

/- Definition 20.48.1 (3): local finite Tor dimension is the canonical open-cover predicate on
derived modules over a ringed space. -/
@[stacks 08CG "(3)"]
#check AlgebraicGeometry.RingedSpace.ModuleDerived.LocallyHasFiniteTorDimension

#check AlgebraicGeometry.RingedSpace.ModuleDerived.HasFiniteTorDimensionOnOpen
#check AlgebraicGeometry.RingedSpace.ModuleDerived.locallyHasFiniteTorDimension_iff_exists_openCover

