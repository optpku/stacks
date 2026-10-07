module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Equivalence
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.FiberedCategoryOver.Groupoids

open scoped Bicategory

universe u v w

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
variable (F : X ⟶ Y)

/- Lemma 4.35.10: a morphism of categories fibred in groupoids over `C` is fully faithful if and
only if its canonical diagonal is an equivalence over the base. -/
@[stacks 04Z7]
#check (Hom.diagonal.fullyFaithful_iff_isEquivalence.{u, v, w} F :
  Nonempty (toBasedFunctor F).FullyFaithful ↔
    BasedFunctor.IsEquivalence (toBasedFunctor (Hom.diagonal F)))

end CategoryTheory.FiberedCategoryOver.Groupoids
