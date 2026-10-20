module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
import StacksCheckRecall

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (F G : CohomologicalDeltaFunctor A B)

/- Definition 12.12.2 [010R]: a morphism of cohomological delta functors is a degreewise family
of natural transformations compatible with the connecting morphisms. -/
@[stacks 010R]
#check (CohomologicalDeltaFunctor.Hom F G : Type _)

#check CohomologicalDeltaFunctor.Hom.app
#check CohomologicalDeltaFunctor.Hom.comm

end CategoryTheory
