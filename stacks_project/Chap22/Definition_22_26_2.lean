module

public import ReasLib.Algebra.Category.DifferentialGraded.Functor
import StacksCheckRecall

universe u v w x y

variable {R : Type u} [CommRing R]
variable (A : Type v) (B : Type w)
variable [DifferentialGradedCategory R A] [DifferentialGradedCategory R B]

/- Definition 22.26.2 [09L6]: an enrichment-preserving functor between differential graded
categories is canonically represented by `DifferentialGradedCategory.DgFunctor`. -/
@[stacks 09L6] #check
  (DifferentialGradedCategory.DgFunctor R A B : Type _)
