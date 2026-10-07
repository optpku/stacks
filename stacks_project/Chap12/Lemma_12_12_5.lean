module

public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor
import StacksCheckRecall

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable (F : A ⥤ B) {G H : CohomologicalDeltaFunctor A B}
variable [G.IsUniversal] [H.IsUniversal]
variable (eG : (G 0).obj ≅ F) (eH : (H 0).obj ≅ F)

/- Lemma 12.12.5 [010U]: universal cohomological delta functors extending the same degree-zero
functor are uniquely isomorphic. -/
@[stacks 010U]
#check (IsUniversal.uniqueIso eG eH :
  ∃! e : G ≅ H, e.hom.app 0 = eG.hom ≫ eH.inv)

end CategoryTheory.CohomologicalDeltaFunctor
