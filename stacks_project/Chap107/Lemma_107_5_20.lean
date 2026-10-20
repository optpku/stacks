module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.FiniteTypePoints
import StacksCheckRecall

/-!
# Finite-type points realizing mixed local dimension

A locally Noetherian algebraic stack has a finite-type point of any open
immersion source realizing the mixed local dimensions of the ambient stack
and of the open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.5.20: if `X` is a locally Noetherian algebraic stack and
`ι : V ⟶ X` is an open immersion of algebraic stacks, then for any
`x : Points V` there is a finite type point `x0 : Points V` such that
`dimensionAt (Points.map ι x0) = dimensionAt x`. -/
@[stacks 0DS1]
#check (AlgebraicGeometry.AlgebraicStack.exists_isFiniteTypePoint_dimensionAt_eq :
  ∀ {S : Scheme.{u}} {X V : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack V] [IsLocallyNoetherian X] [IsLocallyNoetherian V]
    (ι : V ⟶ X) [Groupoids.Hom.OpenImmersion ι] (x : Points V),
    ∃ x0 : Points V, IsFiniteTypePoint x0 ∧
      dimensionAt (Points.map ι x0) = dimensionAt x)

end AlgebraicGeometry.AlgebraicStack
