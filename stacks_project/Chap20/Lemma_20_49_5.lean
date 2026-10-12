/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Characterization
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.5: perfect derived modules are exactly the pseudo-coherent derived modules that
locally have finite Tor dimension. -/
@[stacks 08CQ]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.isPseudoCoherent_and_locallyHasFiniteTorDimension
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.isPseudoCoherent
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.locallyHasFiniteTorDimension
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent.isPerfect_of_locallyHasFiniteTorDimension
