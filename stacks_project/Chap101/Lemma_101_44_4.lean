module

public import stacks_project.Chap101.Lemma_101_44_4_LocalCompleteIntersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.44.4: if `Y ⟶ Z` is smooth and `X ⟶ Z` is a local complete
intersection morphism, then `f : X ⟶ Y` is a local complete intersection
morphism. -/
@[stacks 0CJ6] #check
  (IsLocalCompleteIntersection.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Smooth g] [IsLocalCompleteIntersection (f ≫ g)],
      IsLocalCompleteIntersection f)
