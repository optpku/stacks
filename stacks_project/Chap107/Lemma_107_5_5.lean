/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap107.Remark_107_5_3_RelativeDimension

/-!
# Dimension of a stack via a smooth algebraic-space chart

A smooth morphism from an algebraic space to a locally Noetherian algebraic
stack computes the local dimension of the stack as the presentation difference
of the source dimension and the Definition 107.5.2 fibre dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 107.5.5: if `X` is a locally Noetherian algebraic stack and
`f : U.toGroupoids ⟶ X` is a smooth morphism from an algebraic space, then for
any `u ∈ |U|` mapping to `x ∈ |X|` one has
`dimensionAt x = dimensionDiff (AlgebraicSpace.dimensionAt u) (fiberDimensionAt f u)`,
where `fiberDimensionAt` is the relative dimension of Definition 107.5.2 and
`dimensionAt x` is as in Properties of Stacks, Definition 100.12.2. -/
@[stacks 0DRJ]
theorem dimensionAt_eq_dimensionDiff_fiberDimensionAt {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (f : U.toGroupoids ⟶ X)
    [Smooth f] [LocallyOfFiniteType f] (u : AlgebraicSpace.Points U) :
    dimensionAt (Points.map f (Points.ofAlgebraicSpace u)) =
      dimensionDiff (AlgebraicSpace.dimensionAt u) (fiberDimensionAt f u) :=
  sorry

/-- The smooth chart formula for `dimensionAt` with a representing fibre for
`dim_u(U_x)` as the subtrahend. -/
theorem dimensionAt_eq_dimensionDiff_of_relativeDimensionChoice {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (f : U.toGroupoids ⟶ X)
    [Smooth f] [LocallyOfFiniteType f] (u : AlgebraicSpace.Points U)
    (w : RelativeDimensionChoice f u) :
    dimensionAt (Points.map f (Points.ofAlgebraicSpace u)) =
      dimensionDiff (AlgebraicSpace.dimensionAt u) w.dimension :=
  sorry

end AlgebraicGeometry.AlgebraicStack
