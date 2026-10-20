module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FiniteTypePoints
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Finite-type points realizing local dimension

Every point of an open substack of a locally Noetherian algebraic stack admits
a finite-type point in that open whose ambient dimension equals the local
dimension at the given point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For an open immersion `ι : V ⟶ X` of locally Noetherian algebraic stacks,
every point `x` of `V` admits a finite-type point `x0` of `V` whose dimension
in `X` equals the dimension of `V` at `x`. -/
@[stacks 0DS1]
theorem exists_isFiniteTypePoint_dimensionAt_eq {S : Scheme.{u}} {X V : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack V] [IsLocallyNoetherian X] [IsLocallyNoetherian V]
    (ι : V ⟶ X) [OpenImmersion ι] (x : Points V) :
    ∃ x0 : Points V, IsFiniteTypePoint x0 ∧
      dimensionAt (Points.map ι x0) = dimensionAt x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
