/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent
import StacksCheckRecall

@[expose] public section

/- Definition 20.47.1: pseudo-coherence for complexes, derived modules, and module sheaves on a
ringed space is owned by the reusable RingedSpace facade. -/
@[stacks 08CB] #check @AlgebraicGeometry.RingedSpace.CochainComplex.IsMPseudoCoherent

#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsPseudoCoherent
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPseudoCoherent
#check @SheafOfModules.IsMPseudoCoherent
#check @SheafOfModules.IsPseudoCoherent

