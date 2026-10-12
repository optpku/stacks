/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Triangulated
import StacksCheckRecall

@[expose] public section

/- Lemma 20.48.6: the three distinguished-triangle closure statements for Tor-amplitude on
`D(𝒪_X)` are owned by the ringed-space `ModuleDerived.TorAmplitude` namespace. -/
@[stacks 08CJ "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude.obj₃_of_distinguished

@[stacks 08CJ "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude.obj₂_of_distinguished

@[stacks 08CJ "(3)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude.obj₁_of_distinguished

#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.obj₃_of_distinguished
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.obj₂_of_distinguished
#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.obj₁_of_distinguished
