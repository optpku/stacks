module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.Noetherian.Topology

/-!
# Points of locally Noetherian algebraic stacks

The points space of a locally Noetherian algebraic stack is locally Noetherian, and it is
Noetherian when the algebraic stack is also quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian

/-- The points space of a locally Noetherian algebraic stack is a locally Noetherian topological
space. -/
theorem locallyNoetherianSpace {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] (τ : TopologicalSpace (Points X))
    (hτ : IsPointsTopology X τ) :
    @TopologicalSpace.LocallyNoetherianSpace (Points X) τ :=
  sorry

/-- The points space of a quasi-compact locally Noetherian algebraic stack is a Noetherian
topological space. -/
theorem noetherianSpace {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsLocallyNoetherian X]
    (τ : TopologicalSpace (Points X)) (hτ : IsPointsTopology X τ) :
    @TopologicalSpace.NoetherianSpace (Points X) τ :=
  sorry

/-- The canonical topology on the points of a locally Noetherian algebraic stack is locally
Noetherian. -/
instance instLocallyNoetherianSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsLocallyNoetherian X] :
    @TopologicalSpace.LocallyNoetherianSpace (Points X) (Points.topology X) :=
  locallyNoetherianSpace X (Points.topology X) (isPointsTopology_pointsTopology X)

/-- The canonical topology on the points of a quasi-compact locally Noetherian algebraic stack
is Noetherian. -/
instance instNoetherianSpacePoints {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] [IsQuasiCompact X] [IsLocallyNoetherian X] :
    @TopologicalSpace.NoetherianSpace (Points X) (Points.topology X) :=
  noetherianSpace X (Points.topology X) (isPointsTopology_pointsTopology X)

end AlgebraicGeometry.AlgebraicStack.IsLocallyNoetherian
