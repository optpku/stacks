module

import ReasLib.CategoryTheory.Pretriangulated.BrownRepresentability
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 13.39.2

The reusable owner works with the neutral Brown-representability-set predicate and records both
left-adjoint existence and the existence of a triangulated right adjoint.
-/

namespace CategoryTheory.Functor.Brown.Set

/- The left-adjoint companion to Proposition 13.39.2. -/
#check @isLeftAdjoint

/- Proposition 13.39.2 (`0GYH`): existence of a triangulated right adjoint. -/
@[stacks 0GYH] #check @hasTriangulatedRightAdjoint

end CategoryTheory.Functor.Brown.Set
