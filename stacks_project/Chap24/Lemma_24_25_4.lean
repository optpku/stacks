/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Injective
import StacksCheckRecall

/-!
# Lemma 24.25.4

The product closure of graded-injective objects is the generic product instance for
`CategoryTheory.Functor.IsInjectiveObj`.
-/

@[expose] public section

/- Lemma 24.25.4 (0FSR): a product of objects whose images are injective remains injective after applying
a product-preserving functor. -/
@[stacks 0FSR] #check @CategoryTheory.Functor.instIsInjectiveObjProduct
