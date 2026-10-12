/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Functor.Derived.Pointwise
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.14.4

Pointwise derived-definedness is transported by Mathlib's canonical localization theorem.
The two denominator-inversion consequences are provided by the neutral ReasLib leaf.
-/

@[stacks 05SB] #check @CategoryTheory.Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem

@[stacks 05SB] #check @CategoryTheory.Functor.totalRightDerived_isInvertedBy

@[stacks 05SB] #check @CategoryTheory.Functor.totalRightDerived_map_isIso_of_mem

@[stacks 05SB] #check @CategoryTheory.Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem

@[stacks 05SB] #check @CategoryTheory.Functor.totalLeftDerived_isInvertedBy

@[stacks 05SB] #check @CategoryTheory.Functor.totalLeftDerived_map_isIso_of_mem
