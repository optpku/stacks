module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Existence
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.14

The two denominator-cover criteria are neutral existence API for pointwise derived functors.
-/

@[stacks 05T1] #check
  @CategoryTheory.Functor.RightDerived.EverywhereDefined.of_exists_computesAt

@[stacks 05T1] #check
  @CategoryTheory.Functor.LeftDerived.EverywhereDefined.of_exists_computesAt

#check @CategoryTheory.Functor.RightDerived.EverywhereDefined.hasPointwise_of_exists_computesAt
#check @CategoryTheory.Functor.LeftDerived.EverywhereDefined.hasPointwise_of_exists_computesAt
