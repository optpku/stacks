/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.SeparationDiagram
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 78.29.1: for a groupoid in algebraic spaces, the canonical stabilizer diagram
commutes, its two left horizontal maps are isomorphisms, and its right square is a
fibre product square. -/
@[stacks 0454] #check
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
