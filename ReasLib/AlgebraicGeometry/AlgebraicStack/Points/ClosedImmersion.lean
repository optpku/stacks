module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Closed immersions on algebraic-stack points

The image of a closed immersion is closed in the canonical topology on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Points

/-- The range of the map on points induced by a closed immersion of algebraic
stacks is closed. -/
theorem isClosed_range_of_closedImmersion {S : Scheme.{u}} {Y X : GroupoidsOver S}
    [AlgebraicStack Y] [AlgebraicStack X] (i : Y ⟶ X)
    [Groupoids.Hom.ClosedImmersion i] : IsClosed (Set.range (map i)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Points
