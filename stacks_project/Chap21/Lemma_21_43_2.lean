module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Closure
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ModulesOnCategory

/- Lemma 21.43.2 (1): strict fullness is supplied by the presentation-independent ReasLib
comparison-locus owner. -/
@[stacks 0GYW "(1)"]
#check qc_isClosedUnderIsomorphisms

/- Lemma 21.43.2 (2): stability under retracts is supplied by the same owner. -/
@[stacks 0GYW "(2)"]
#check qc_isStableUnderRetracts

/- Lemma 21.43.2 (3): exact comparison data makes the comparison locus triangulated. -/
@[stacks 0GYW "(3)"]
#check qc_isTriangulated

/- Lemma 21.43.2 (4): the general colimit theorem specializes to arbitrary direct sums. -/
@[stacks 0GYW "(4)"]
#check qc_isClosedUnderDirectSums

end CategoryTheory.ModulesOnCategory
