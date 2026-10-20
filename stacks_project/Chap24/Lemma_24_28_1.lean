/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Left
import StacksCheckRecall

@[expose] public section

/-
Lemma 24.28.1 (tag 0FTF): a denominator-cofinal class of good objects on which a functor
inverts denominators supplies its left-derived functor, and every good object computes its
left-derived value.  The reusable formulation is independent of homotopy categories and
differential graded modules: `LeftDerived.EverywhereDefined.of_subset` retains the stronger
source-definedness assertion, while the pointwise and total-derived consequences follow through
the canonical bridges below.
-/
@[stacks 0FTF "good objects compute the left-derived functor"]
#check @CategoryTheory.Functor.LeftDerived.ComputesAt.of_mem_subset
@[stacks 0FTF "cofinal good objects define the left-derived functor"]
#check @CategoryTheory.Functor.LeftDerived.EverywhereDefined.of_subset
#check @CategoryTheory.Functor.LeftDerived.EverywhereDefined.hasPointwise_of_subset
#check @CategoryTheory.Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
