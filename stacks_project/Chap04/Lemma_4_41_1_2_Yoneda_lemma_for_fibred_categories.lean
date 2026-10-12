/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Basic.Chosen
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable (X : FiberedCategoryOver C) (U : C)

/- Lemma 4.41.1 (2-Yoneda lemma for fibred categories): the canonical neutral statement is
`FiberedCategoryOver.YonedaSlice.evaluation.isEquivalence`. -/
@[stacks 0GWI]
#check (FiberedCategoryOver.YonedaSlice.evaluation.isEquivalence X U :
  (FiberedCategoryOver.YonedaSlice.evaluation X U).IsEquivalence)

end CategoryTheory
