/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Right
import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Left
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.15

The denominator-cofinal good-subset criteria are neutral pointwise-derived-functor API. Their
right and left forms live in separate ReasLib leaves so downstream developments can import only
the variance they use.
-/

@[stacks 06XN] #check @CategoryTheory.Functor.RightDerived.ComputesAt.of_mem_subset
@[stacks 06XN] #check
  @CategoryTheory.Functor.RightDerived.EverywhereDefined.hasPointwise_of_subset
@[stacks 06XN] #check @CategoryTheory.Functor.LeftDerived.ComputesAt.of_mem_subset
@[stacks 06XN] #check
  @CategoryTheory.Functor.LeftDerived.EverywhereDefined.hasPointwise_of_subset
