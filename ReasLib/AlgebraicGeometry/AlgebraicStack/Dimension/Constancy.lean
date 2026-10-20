module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.PseudoCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Jacobson
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Irreducible

/-!
# Constancy of dimension on irreducible algebraic stacks

On a Jacobson, pseudo-catenary, locally Noetherian algebraic stack whose space
of points is irreducible, the dimension at a point is independent of the
chosen point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- On a Jacobson, pseudo-catenary, locally Noetherian algebraic stack with
irreducible space of points, the dimensions at any two points are equal. -/
@[stacks 0DRX]
theorem dimensionAt_eq_of_irreducible {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] [IsJacobson X]
    [IsPseudoCatenary X] [IsIrreducible X] (x y : Points X) :
    dimensionAt x = dimensionAt y := sorry

/-- On a Jacobson, pseudo-catenary, locally Noetherian algebraic stack with
irreducible space of points, the global dimension equals the dimension at
every point. -/
theorem dimension_eq_dimensionAt_of_irreducible {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
    [IsJacobson X] [IsPseudoCatenary X] [IsIrreducible X] (x : Points X) :
    dimension X = dimensionAt x := sorry

end AlgebraicGeometry.AlgebraicStack
