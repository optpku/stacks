/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap107.Definition_107_5_14_PseudoCatenary
public import stacks_project.Chap107.Lemma_107_5_24_Jacobson

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

/-- Lemma 107.5.17: if `X` is a Jacobson, pseudo-catenary, locally Noetherian
algebraic stack for which `|X|` is irreducible, then `dimensionAt` is a
constant function on `Points X`. -/
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
