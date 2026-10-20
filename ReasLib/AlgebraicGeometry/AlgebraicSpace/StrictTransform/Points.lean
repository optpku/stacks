module

public import Mathlib.Topology.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support

/-!
# Point sets of strict transforms of closed subspaces

The strict-transform support of a closed subspace is the closure of its inverse
image away from the center.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The point-set support of the strict transform of a closed subspace along a
blowup is the closure of its inverse image away from the center. -/
def strictTransformPointsSet {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (b : B' ⟶ B) (center Z : ClosedSubspace B) : Set (Points B') :=
  closure (Points.map b ⁻¹' (Z.pointsSet \ center.pointsSet))

/-- The strict-transform support of a closed subspace is the closure of its
inverse image away from the center. -/
theorem strictTransformPointsSet_eq {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (b : B' ⟶ B) (center Z : ClosedSubspace B) :
    strictTransformPointsSet b center Z =
      closure (Points.map b ⁻¹' (Z.pointsSet \ center.pointsSet)) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
