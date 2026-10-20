module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
import StacksCheckRecall

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory

variable (A : Type uA) [Category.{vA} A] [Abelian A]
variable (B : Type uB) [Category.{vB} B] [Abelian B]

/- Definition 12.12.1 [010Q]: a cohomological delta functor consists of additive degreewise
functors, connecting morphisms for short exact sequences, long exactness, and naturality. -/
@[stacks 010Q]
#check (CohomologicalDeltaFunctor A B : Type _)

#check CohomologicalDeltaFunctor.F
#check CohomologicalDeltaFunctor.δ
#check CohomologicalDeltaFunctor.exact₅
#check CohomologicalDeltaFunctor.δ_naturality

end CategoryTheory
