module

public import stacks_project.Chap101.Lemma_101_35_6_Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.35.6: let `X`, `Y` be algebraic stacks étale over an algebraic stack
`Z`. Any morphism `X ⟶ Y` over `Z` is étale. -/
@[stacks 0CIR] #check
  (Etale.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
      (f : X ⟶ Y) (g : Y ⟶ Z)
      [Etale (f ≫ g)] [Etale g],
      Etale f)
