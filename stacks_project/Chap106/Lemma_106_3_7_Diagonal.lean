module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Thickening.Diagonal

/-!
# Diagonal squares of morphisms of thickenings

The canonical self-product map is a thickening, and the square of relative
diagonals is a 2-fibre-product square.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.selfMap_isThickening :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (w : f ≫ j ≅ i ≫ f'),
      IsThickening (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.selfMap w))

#check (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.diagonalCone.isBilimit :
    ∀ {S : Scheme.{u}} {X X' Y Y' : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack X'] [AlgebraicStack Y] [AlgebraicStack Y']
      {i : X ⟶ X'} {j : Y ⟶ Y'} [IsThickening i] [IsThickening j]
      {f : X ⟶ Y} {f' : X' ⟶ Y'} (w : f ≫ j ≅ i ≫ f'),
      (AlgebraicGeometry.AlgebraicStack.IsThickening.diagonalSquare.diagonalCone w).IsBilimit)
