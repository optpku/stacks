module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap107.«107_5_19_1_Reduced»

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- 107.5.19.1: if `X` is a locally Noetherian algebraic stack and `x` is a point
of `|X|`, then `dimensionAt x` is at most the supremum of `dimensionAt` of the
induced reduced irreducible-component closed substacks of `|X|` through `x`. -/
@[stacks 0DS0]
theorem dimensionAt_le_iSup_irreducibleComponents_through
    {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsLocallyNoetherian X] (x : Points X)
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    dimensionAt x ≤
      ⨆ T : { T : @irreducibleComponents (Points X) τ // x ∈ (T : Set (Points X)) },
        dimensionAt (irreducibleComponentSubstack.point hτ T.1 x T.2) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
