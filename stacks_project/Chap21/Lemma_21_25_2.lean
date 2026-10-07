module

public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.BoundedBasis
import StacksCheckRecall

@[expose] public section

/-!
Lemma 21.25.2 (0D6S).  The bounded-basis completeness criterion is owned by
`CategoryTheory.DerivedCategory.CohomologyIn.isIso_of_boundedBasis`.  This chapter file is a
source-facing recall only; downstream proofs should import the ReasLib owner directly.
-/

open CategoryTheory

@[stacks 0D6S]
#check @DerivedCategory.CohomologyIn.isIso_of_boundedBasis

#check @GrothendieckTopology.BoundedCohomologyBasis
#check @DerivedCategory.Truncation.Lower.Comparison.Exists

end
