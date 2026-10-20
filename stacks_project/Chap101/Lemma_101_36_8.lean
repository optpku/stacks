module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.36.8: if `f ≫ g` is unramified and `g` is DM, then `f` is unramified. -/
@[stacks 0CIZ] #check
  (AlgebraicGeometry.AlgebraicStack.Unramified.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Unramified (f ≫ g)] [DM g],
      Unramified f)
