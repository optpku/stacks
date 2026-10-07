module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer

/-!
# Pre-relation of a groupoid in algebraic spaces

This module retains typed compatibility checks for the reusable groupoid and
pre-relation API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

#check (AlgebraicGeometry.GroupoidAlgebraicSpace :
  (B : AlgebraicSpace S) → Type (u + 1))

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.j :
  {B : AlgebraicSpace S} →
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      G.R ⟶ G.U ⨯ G.U)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation :
  {B : AlgebraicSpace S} →
    (G : AlgebraicGeometry.GroupoidAlgebraicSpace B) →
      AlgebraicGeometry.AlgebraicSpace.PreRelation G.U)

end AlgebraicGeometry
