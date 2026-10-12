/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties
import ReasLib.CategoryTheory.Functor.Derived.RightDerived
import StacksCheckRecall

@[expose] public section

/- Lemma 13.16.3 is owned by the reusable right-derived properties API.
The bounded-below results are in
`ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Properties`,
and the injective-resolution results are in
`ReasLib.CategoryTheory.Functor.Derived.RightDerived`. -/
@[stacks 05TD] #check @CategoryTheory.Functor.RightDerived.degree.isZero_of_neg
@[stacks 05TD] #check @CategoryTheory.Functor.RightDerived.zero.preservesFiniteLimits
@[stacks 05TD] #check @CategoryTheory.Functor.RightDerived.zero.isIso_iff_preservesFiniteLimits
@[stacks 05TD] #check @CategoryTheory.Functor.RightDerived.Bounded.degree.isZero_of_neg
@[stacks 05TD] #check @CategoryTheory.Functor.RightDerived.Bounded.zero.preservesFiniteLimits
@[stacks 05TD] #check @CategoryTheory.Functor.RightDerived.Bounded.zero.isIso_iff_preservesFiniteLimits
@[stacks 05TD] #check @CategoryTheory.Functor.rightDerivedZero_preservesFiniteLimits
@[stacks 05TD] #check @CategoryTheory.Functor.isIso_toRightDerivedZero_iff_preservesFiniteLimits

end
