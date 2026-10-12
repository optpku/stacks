/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow.Composition
import StacksCheckRecall

@[expose] public section

/- Lemma 20.13.7: for composable morphisms of ringed spaces, the canonical map from
bounded-below derived pushforward along the composite to the composite of the two derived
pushforwards is an isomorphism. -/
@[stacks 01F5]
#check @AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus.compIso

#check @AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus.compComparison
#check @AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus.compComparison_isIso
