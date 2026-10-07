module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Stabilizer

/-!
# Stabilizer groups of groupoids in algebraic spaces

This module retains typed compatibility checks for the reusable stabilizer API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.stabilizer :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} → {U : Over B} →
    PreRelation U → Over U)

#check (AlgebraicGeometry.AlgebraicSpace.PreRelation.stabilizerToArrows :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} → {U : Over B} →
    (P : PreRelation U) → P.stabilizer.left ⟶ P.left)

end AlgebraicGeometry.AlgebraicSpace.PreRelation

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open CartesianMonoidalCategory MonoidalCategory MonObj

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerComposablePair :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : GroupoidAlgebraicSpace B) →
      (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).left ⟶
        pullback G.s G.t)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerMul :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : GroupoidAlgebraicSpace B) →
      G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer ⟶
        G.toPreRelation.stabilizer)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerOne :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : GroupoidAlgebraicSpace B) →
      𝟙_ (Over G.U) ⟶ G.toPreRelation.stabilizer)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerInv :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : GroupoidAlgebraicSpace B) →
      G.toPreRelation.stabilizer ⟶ G.toPreRelation.stabilizer)

#check (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizer :
  {S : Scheme.{u}} → {B : AlgebraicSpace S} →
    (G : GroupoidAlgebraicSpace B) → Grp (Over G.U))

end AlgebraicGeometry.GroupoidAlgebraicSpace
