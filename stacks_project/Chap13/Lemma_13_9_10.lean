module

import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.SplittingIndependence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.10

The independence of the triangle attached to a degreewise splitting is owned by the neutral
homotopy-category leaf `SplittingIndependence`.  The source entry keeps only the labeled recall and
the atomic correction, homotopy, and triangle-isomorphism checks.
-/

namespace CochainComplex

@[stacks 05SS]
#check @DegreewiseSplit.Splitting.correction
@[stacks 05SS]
#check @DegreewiseSplit.Splitting.correction_spec
@[stacks 05SS]
#check @DegreewiseSplit.Splitting.homotopy
@[stacks 05SS]
#check @DegreewiseSplit.Splitting.eq_in_homotopyCategory
@[stacks 05SS]
#check @DegreewiseSplit.Splitting.triangleIso

end CochainComplex
