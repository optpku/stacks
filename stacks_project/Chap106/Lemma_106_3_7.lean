module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Diagonal
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.AlgebraicStack.IsThickening
open scoped Bicategory

universe u

/- Lemma 106.3.7 (1): a morphism of thickenings `(f, f') : (X ⊂ X') ⟶ (Y ⊂ Y')`
of algebraic stacks induces a thickening
`X ×_Y X ⟶ X' ×_{Y'} X'` of the chosen self 2-fibre products. -/
@[stacks 0BPU] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.selfMap_isThickening :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (w : f ≫ j ≅ i ≫ f'),
      IsThickening (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.selfMap w))

/- Lemma 106.3.7 (2): the canonical square of relative diagonals Δ, Δ' with
left leg `X ⟶ X'` is a 2-fibre-product square. -/
@[stacks 0BPU] #check (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.diagonalCone.isBilimit :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (w : f ≫ j ≅ i ≫ f'),
      (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.diagonalCone w).IsBilimit)
