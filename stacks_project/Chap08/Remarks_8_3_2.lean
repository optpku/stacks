module

public import ReasLib.CategoryTheory.Sites.Descent.Family.Coherence
import StacksCheckRecall

@[expose] public section

/-!
# Remarks 8.3.2 -- Diagonal and switched-overlap coherence

The canonical owner is the family-descent coherence API in ReasLib.  It is formulated through
the general `Pseudofunctor.DescentData.iso` comparison map, so it does not depend on the older
chapter-specific `DescentData'` encoding or on a particular chosen-pullback presentation.
-/

namespace CategoryTheory

/- The comparison isomorphisms themselves are reusable data; the following identities are their
coherence readouts. -/
#check @DescentDatum.diagonalComparisonIso
#check @DescentDatum.overlapComparisonIso
#check @DescentDatum.switchedOverlapComparisonIso

/- Remarks 8.3.2 (1): the diagonal self-comparison is the identity. -/
@[stacks 026C "(1) diagonal comparison"]
#check @DescentDatum.Comparison.diagonal_eq_refl

/- Reversing an overlap comparison gives its symmetric comparison. -/
#check @DescentDatum.Comparison.switched_eq_symm

/- Remarks 8.3.2 (2): an overlap comparison followed by the comparison with switched legs is
the identity. -/
@[stacks 026C "(2) overlap comparison with switched legs"]
#check @DescentDatum.Comparison.comp_switched_eq_refl

end CategoryTheory
