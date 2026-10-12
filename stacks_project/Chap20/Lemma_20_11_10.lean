/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Pushforward
import StacksCheckRecall

@[expose] public section

/- Lemma 20.11.10 (1) (01EX): pushforwards of injective module sheaves are Cech-acyclic. -/
@[stacks 01EX]
#check @AlgebraicGeometry.RingedSpace.ModuleCech.pushforward_isAcyclic_of_injective

/- Lemma 20.11.10 (2) (01EX): their positive sheaf cohomology vanishes on every open. -/
@[stacks 01EX]
#check @AlgebraicGeometry.RingedSpace.ModuleCohomology.isZero_pushforward_of_injective

#check @AlgebraicGeometry.RingedSpace.ModuleCech.isZero_pushforward_of_injective
