/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalCriterion
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
variable (X : Groupoids C)

/- Lemma 4.42.6: for a category fibred in groupoids `X` over `C`, relative representability of
its canonical diagonal is equivalent to relative representability of every morphism
`G : C/U ⟶ X` from a slice fibration. -/
@[stacks 02YA]
#check (relativelyRepresentable.diagonal_iff X :
  relativelyRepresentable (diagonal X) ↔
    ∀ {U : C} (G : slice U ⟶ X), relativelyRepresentable G)

end FiberedCategoryOver.Groupoids

end CategoryTheory
