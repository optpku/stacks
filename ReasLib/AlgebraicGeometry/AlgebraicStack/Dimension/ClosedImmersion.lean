module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Dimension along closed immersions of algebraic stacks

A closed immersion of locally Noetherian algebraic stacks cannot increase
dimension at a point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The dimension at a point of a locally Noetherian algebraic stack is at most
the dimension at its image under a closed immersion into a locally Noetherian
algebraic stack. -/
@[stacks 0DRY]
theorem dimensionAt_le_of_closedImmersion {S : Scheme.{u}} {Z X : GroupoidsOver S}
    [AlgebraicStack Z] [AlgebraicStack X] [IsLocallyNoetherian Z] [IsLocallyNoetherian X]
    (i : Z ⟶ X) [ClosedImmersion i] (z : Points Z) :
    dimensionAt z ≤ dimensionAt (Points.map i z) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
