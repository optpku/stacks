/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.SeparationDiagram

/-!
# The stabilizer diagram of a groupoid in algebraic spaces

This module retains typed compatibility checks for the reusable stabilizer diagram API.
-/

@[expose] public section

open CategoryTheory Limits

universe u

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerDiagram_comm :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      CommSq (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceUnitMap G)
        (pullback.diagonal G.toPreRelation.hom)
        (AlgebraicGeometry.GroupoidAlgebraicSpace.unitBaseChangeMap G)
        (AlgebraicGeometry.GroupoidAlgebraicSpace.differenceMap G))

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceUnitIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.R ≅ AlgebraicGeometry.GroupoidAlgebraicSpace.sourceFiber G)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceUnitIso_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceUnitIso G).hom =
        AlgebraicGeometry.GroupoidAlgebraicSpace.sourceUnitMap G)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.differenceIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      AlgebraicGeometry.GroupoidAlgebraicSpace.relationSelfPullback G ≅
        AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerFiber G)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.differenceIso_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      (AlgebraicGeometry.GroupoidAlgebraicSpace.differenceIso G).hom =
        AlgebraicGeometry.GroupoidAlgebraicSpace.differenceMap G)

#check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.unitSquare_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      IsPullback (AlgebraicGeometry.GroupoidAlgebraicSpace.sourceProjection G)
        (AlgebraicGeometry.GroupoidAlgebraicSpace.unitBaseChangeMap G)
        (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerOneLift G)
        (AlgebraicGeometry.GroupoidAlgebraicSpace.stabilizerProjection G))
