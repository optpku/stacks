module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
import StacksCheckRecall

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (F : CohomologicalDeltaFunctor A B)

/- Definition 12.12.3 [010S]: universality is the unique extension of every degree-zero natural
transformation to a morphism of cohomological delta functors. -/
@[stacks 010S]
#check (CohomologicalDeltaFunctor.IsUniversal F : Prop)

#check CohomologicalDeltaFunctor.IsUniversal.existsUnique_hom

end CategoryTheory
