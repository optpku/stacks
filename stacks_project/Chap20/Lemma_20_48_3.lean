/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.FlatRepresentative
import StacksCheckRecall

@[expose] public section

/- Lemma 20.48.3: Tor-amplitude in `[a, b]` is equivalent to admitting a termwise-flat
representative supported in `[a, b]`. -/
@[stacks 08CI]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.hasTorAmplitudeIn_iff_hasFlatRepresentativeIn

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.HasFlatRepresentativeIn
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.hasFlatRepresentativeIn_iff
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.hasFlatRepresentativeIn_of_hasTorAmplitudeIn
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.HasFlatRepresentativeIn.hasTorAmplitudeIn
