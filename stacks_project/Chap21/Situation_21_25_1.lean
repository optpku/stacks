module

public import ReasLib.CategoryTheory.Sites.BoundedCohomologyBasis
import StacksCheckRecall

@[expose] public section

/-!
Situation `21.25.1` is a source-facing recall.  The reusable data owner is
`CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis` in ReasLib; keeping this file as a
recall prevents downstream statements from depending on a chapter implementation.
-/

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology

@[stacks 0D6R] #check @BoundedCohomologyBasis
@[stacks 0D6R] #check @BoundedCohomologyBasis.hasEnoughObjects
@[stacks 0D6R] #check @BoundedCohomologyBasis.exists_coveringSystem_refinement
@[stacks 0D6R] #check @BoundedCohomologyBasis.higherCohomology_isZero

end CategoryTheory.GrothendieckTopology

end
