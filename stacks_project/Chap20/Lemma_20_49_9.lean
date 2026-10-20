module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Retracts
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.9: if a binary biproduct of derived `𝒪_X`-modules is perfect, then both
summands are perfect. -/
@[stacks 08CS]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_summands_of_biprod

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_left_of_biprod
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_right_of_biprod
