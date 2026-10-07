module

import ReasLib.CategoryTheory.Pretriangulated.CompactObject.Factorization
import StacksCheckRecall

@[expose] public section

-- Lemma 13.37.4: compact maps into a generating-family approximation factor through a finite
-- coproduct-generated triangulated envelope, with an available positive-stage refinement.
@[stacks 09SP] #check @CategoryTheory.IsGeneratingFamilyApproximation.compactFactorization
#check @CategoryTheory.IsGeneratingFamilyApproximation.compactFactorizationAtStage
