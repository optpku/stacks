module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Power
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {A : Type u} [CommRing A]

/- Example 20.39.3 (0H3E): the reusable owner is the derived-global-sections specialization of
the endomorphism-power comparison. -/
open AlgebraicGeometry.RingedSpace.ModuleDerived.GlobalSections.Power

@[stacks 0H3E]
#check @existsShiftInverse

@[stacks 0H3E]
#check @augmentation_isIso

end AlgebraicGeometry.RingedSpace
