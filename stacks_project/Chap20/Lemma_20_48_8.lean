module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Triangulated
import StacksCheckRecall

@[expose] public section

/- Lemma 20.48.8: Tor-amplitude in a fixed interval is stable under direct summands.  The
reusable owner exposes both the bundled summand statement and its left/right projections. -/
@[stacks 08CK]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude.summands_of_biprod

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude.left_of_biprod
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.TorAmplitude.right_of_biprod

#check @CategoryTheory.DerivedCategory.DerivedTensor.TorAmplitude.summands_of_biprod
#check @CategoryTheory.DerivedCategory.DerivedTensor.HasTorAmplitudeIn.ofRetract
