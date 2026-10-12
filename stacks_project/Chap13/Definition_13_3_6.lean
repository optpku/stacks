/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.DeltaFunctor.Definition
import StacksCheckRecall

@[expose] public section

/- Definition 13.3.6 is owned by the reusable pretriangulated delta-functor API. -/
@[stacks 0150] #check @CategoryTheory.DeltaFunctor
@[stacks 0150] #check @CategoryTheory.DeltaFunctor.triangle
@[stacks 0150] #check @CategoryTheory.DeltaFunctor.triangleMap

end
