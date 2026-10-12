/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Local
import StacksCheckRecall

@[expose] public section

/- Definition 20.47.1: on a ringed space, `m`-pseudo-coherence is equivalently expressed by
strict-perfect approximations on the members of an open cover. -/
@[stacks 08CB]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isMPseudoCoherent_iff_exists_openCover

#check @AlgebraicGeometry.RingedSpace.CochainComplex.isMPseudoCoherent_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.HasStrictlyPerfectApproximationInDegreeOnOpen
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isMPseudoCoherent_of_isOpenCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent.exists_openCover

