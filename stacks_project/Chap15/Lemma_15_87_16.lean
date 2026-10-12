/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler.ProZero
import StacksCheckRecall

/-!
# Lemma 15.87.16

@stack 091C
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.87.16 (Stacks 091C): a sequential inverse system of abelian groups represents the
zero pro-value exactly when `lim`, `R¹ lim`, and the corresponding `R¹ lim` of its stagewise
countable coproduct vanish.  The canonical pro-side predicate is `Pro.HasValue A 0`; the neutral
bridge API is independent of Chapter 15. -/
@[stacks 091C]
#check @CategoryTheory.Pro.HasValue.zero_iff_limit_and_r1Vanishing_of_countableCoproduct

#check @CategoryTheory.Pro.HasValue.zero_iff_eventuallyZeroTransitions
#check @CategoryTheory.SequentialInverseSystem.Milnor.ProductCone.canonicalR1
