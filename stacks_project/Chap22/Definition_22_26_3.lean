module

public import ReasLib.Algebra.Category.DifferentialGraded.Homotopy
import StacksCheckRecall

universe u v

variable {R : Type u} [CommRing R]
variable (C : Type v) [DifferentialGradedCategory R C]

/- Definition 22.26.3 [09L7]: the category of closed degree-zero morphisms is canonically
represented by `DifferentialGradedCategory.Comp`. -/
@[stacks 09L7] #check (DifferentialGradedCategory.Comp R C : Type v)

/- Definition 22.26.3 [09L7]: the associated homotopy category is canonically represented
by `DifferentialGradedCategory.K`. -/
@[stacks 09L7] #check (DifferentialGradedCategory.K R C : Type v)
