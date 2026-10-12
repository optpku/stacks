/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.DifferentialOperator
import StacksCheckRecall

@[expose] public section

/- Lemma 17.30.5 (0G3Z): each relative de Rham differential of a morphism of ringed spaces is a
differential operator of order at most one. -/
@[stacks 0G3Z]
#check @AlgebraicGeometry.RingedSpace.DeRham.d_isOrderOne
