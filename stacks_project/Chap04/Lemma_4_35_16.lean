/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Factorization
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe u v uX

variable {C : Type u} [Category.{v} C]
variable {X Y :
  FiberedCategoryOver.Groupoids.{u, v, max uX (max u v), v} C}
variable (F : X ⟶ Y)

/- Lemma 4.35.16: every morphism of categories fibred in groupoids factors strictly through an
equivalent groupoid fibration whose morphism to the target is itself fibred in groupoids. The
source-faithful owner is
`FiberedCategoryOver.Groupoids.Factorization.existsEquivalence`. -/
@[stacks 06N7]
#check (FiberedCategoryOver.Groupoids.Factorization.existsEquivalence.{u, v, uX} F :
  ∃ (X' : FiberedCategoryOver.Groupoids.{u, v, max uX (max u v), v} C)
      (e : X ≌ X') (f : X' ⟶ Y),
    e.hom ≫ f = F ∧ Functor.IsFibered.InGroupoids (FiberedCategoryOver.Groupoids.toFunctor f))

end CategoryTheory
