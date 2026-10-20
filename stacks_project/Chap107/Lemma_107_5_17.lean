module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.Constancy
import StacksCheckRecall

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

/- Lemma 107.5.17: if `X` is a Jacobson, pseudo-catenary, locally Noetherian
algebraic stack for which `|X|` is irreducible, then `dimensionAt` is a
constant function on `Points X`. -/
@[stacks 0DRX] #check (AlgebraicGeometry.AlgebraicStack.dimensionAt_eq_of_irreducible :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsLocallyNoetherian X] [IsJacobson X]
      [IsPseudoCatenary X] [IsIrreducible X] (x y : Points X),
      dimensionAt x = dimensionAt y)

/- On a Jacobson, pseudo-catenary, locally Noetherian algebraic stack with
irreducible space of points, the global dimension equals the dimension at
every point. -/
#check (AlgebraicGeometry.AlgebraicStack.dimension_eq_dimensionAt_of_irreducible :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
      [AlgebraicStack X] [IsLocallyNoetherian X] [IsJacobson X]
      [IsPseudoCatenary X] [IsIrreducible X] (x : Points X),
      dimension X = dimensionAt x)

end AlgebraicGeometry.AlgebraicStack
