module

public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap107.Lemma_107_5_24_FiberDimension

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

/-- Lemma 107.5.20: if `X` is a locally Noetherian algebraic stack and
`ι : V ⟶ X` is an open immersion of algebraic stacks, then for any
`x : Points V` there is a finite type point `x0 : Points V` such that
`dimensionAt (Points.map ι x0) = dimensionAt x`. -/
@[stacks 0DS1]
theorem exists_isFiniteTypePoint_dimensionAt_eq {S : Scheme.{u}} {X V : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack V] [IsLocallyNoetherian X] [IsLocallyNoetherian V]
    (ι : V ⟶ X) [OpenImmersion ι] (x : Points V) :
    ∃ x0 : Points V, IsFiniteTypePoint x0 ∧
      dimensionAt (Points.map ι x0) = dimensionAt x :=
  sorry

end AlgebraicGeometry.AlgebraicStack
