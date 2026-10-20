module

public import Mathlib.Topology.NoetherianSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober
public import ReasLib.AlgebraicGeometry.Noetherian.Topology

/-!
# Points of locally Noetherian and Noetherian algebraic spaces

The space of points of a locally Noetherian algebraic space is locally Noetherian, and it is
Noetherian when the algebraic space is also quasi-compact.
The space of points of a Noetherian algebraic space is a sober Noetherian topological space.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian

/-- The point space of a locally Noetherian algebraic space is a locally Noetherian topological
space. -/
instance (priority := 100) locallyNoetherianSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] : TopologicalSpace.LocallyNoetherianSpace (Points X) :=
  sorry

/-- The point space of a quasi-compact locally Noetherian algebraic space is a Noetherian
topological space. -/
instance (priority := 100) noetherianSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsLocallyNoetherian X] : TopologicalSpace.NoetherianSpace (Points X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocallyNoetherian

namespace AlgebraicGeometry.AlgebraicSpace.IsNoetherian

/-- The point space of a Noetherian algebraic space is a Noetherian topological space. -/
instance noetherianSpace {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsNoetherian X] : TopologicalSpace.NoetherianSpace (Points X) :=
  sorry

/-- The point space of a Noetherian algebraic space is sober and Noetherian. -/
theorem sober_noetherian {S : Scheme.{u}} (X : AlgebraicSpace S) [IsNoetherian X] :
    T0Space (Points X) ∧ QuasiSober (Points X) ∧
      TopologicalSpace.NoetherianSpace (Points X) :=
  ⟨(AlgebraicGeometry.AlgebraicSpace.points_sober X).1,
    (AlgebraicGeometry.AlgebraicSpace.points_sober X).2, inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace.IsNoetherian
