module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeSquare
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The category of dotted arrows of a valuative square of algebraic stacks is
thin when the first relative diagonal of the stack morphism is separated. -/
theorem dottedArrow_isThin_of_diagonal_separated
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h_diagonal :
      Groupoids.Hom.has (@AlgebraicSpace.Separated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
    (sq : ValuativeCommSq f) :
    Quiver.IsThin (DottedArrow sq.toCone) :=
  sorry

/-- A quasi-separated first relative diagonal of a morphism of algebraic stacks
is separated if the category of dotted arrows is thin for every valuative square
and every choice of its invertible comparison. -/
@[stacks 0CLR]
theorem diagonal_separated_of_quasiSeparated_of_dottedArrow_isThin
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (h_quasiSeparated :
      Groupoids.Hom.has (@AlgebraicSpace.QuasiSeparated S)
        (Hom.diagonal.{u + 1, u, u + 1} f))
    (h_isThin : ∀ sq : ValuativeCommSq f, Quiver.IsThin (DottedArrow sq.toCone)) :
    Groupoids.Hom.has (@AlgebraicSpace.Separated S)
      (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
