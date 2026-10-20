module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure

/-!
# Reduced point closures as closed subspaces
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The reduced induced closed subspace supported on the closure of a point of
`|Y|`. -/
def pointClosure {S : Scheme.{u}} {Y : AlgebraicSpace S} (y : Points Y) :
    ClosedSubspace Y :=
  (ClosedSubspaceStructure.reduced (Closeds.closure {y})).subspace

/-- The underlying point-set of `pointClosure y` is the topological closure of
`{y}`. -/
theorem pointClosure_pointsSet {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (y : Points Y) :
    (pointClosure y).pointsSet = closure ({y} : Set (Points Y)) :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
