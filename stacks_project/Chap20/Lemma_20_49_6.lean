/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.6: derived pullback along a morphism of ringed spaces preserves perfect
derived module sheaves. -/
@[stacks 09UA]
#check @AlgebraicGeometry.RingedSpace.modulePullbackDerived_isPerfect
