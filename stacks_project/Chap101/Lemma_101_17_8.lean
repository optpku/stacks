module

public import stacks_project.Chap101.Lemma_101_17_8_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.17.8: if `g ∘ f` is locally of finite type then so is `f`. -/
@[stacks 06U9] #check
  (LocallyOfFiniteType.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType (f ≫ g)],
      LocallyOfFiniteType f)
