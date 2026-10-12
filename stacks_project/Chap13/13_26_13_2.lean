/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Filtration.Derived.Finite.Compatibility
import StacksCheckRecall

@[expose] public section

/-!
# Equation 13.26.13.2

The right derived functor and its factorization unit are owned independently from the homotopy
source, so later statements may reuse either layer without reconstructing the composite.
-/

namespace CategoryTheory.FilteredComplex.RightDerived.Finite.LeftExact

/- Equation 13.26.13.2 (`015S`): the bounded-below filtered right derived functor of a left-exact
functor. -/
@[stacks 015S] #check @functor

/- The precise existence condition for the preceding derived functor. -/
#check @Has

/- The canonical factorization from the homotopy-level source. -/
#check @unit

end CategoryTheory.FilteredComplex.RightDerived.Finite.LeftExact
