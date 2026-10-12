/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.UpperResolution
import StacksCheckRecall

@[expose] public section

/- Proposition 13.29.2 is the upper-resolution criterion for constructing an
unbounded total left derived functor.  The reusable bounded computation,
resolution-colimit, pointwise, and total APIs live in ReasLib. -/

@[stacks 0794]
#check @CategoryTheory.Functor.IsBoundedAboveAcyclicClass.hasLeftDerivedFunctor_of_rightExact

end
