/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Tensor
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.8: the derived tensor product of two perfect objects of `D(𝒪_X)` is
perfect. -/
@[stacks 09J5]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.tensor
