module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage.Presheaf
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.Presheaf

/- Remark 20.7.5: the sheafification of a positive cohomology presheaf is zero. -/
@[stacks 03BA "positive cohomology presheaf sheafification vanishing"]
#check @isZero_sheafification_of_pos
