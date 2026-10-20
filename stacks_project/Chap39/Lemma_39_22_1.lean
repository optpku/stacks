/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap39.Lemma_39_22_1_Stabilizer
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u

/- Lemma 39.22.1: for a groupoid scheme, the canonical stabilizer diagram commutes, its
two left horizontal maps are isomorphisms, and its right square is a pullback square. -/
@[stacks 02YH] #check
  (AlgebraicGeometry.GroupoidScheme.stabilizerDiagram_comm :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      CommSq (AlgebraicGeometry.GroupoidScheme.sourceUnitMap G)
        (pullback.diagonal G.toPreRelation.hom)
        (AlgebraicGeometry.GroupoidScheme.unitBaseChangeMap G)
        (AlgebraicGeometry.GroupoidScheme.differenceMap G))

#check
  (AlgebraicGeometry.GroupoidScheme.sourceUnitIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.R ≅ AlgebraicGeometry.GroupoidScheme.sourceFiber G)

#check
  (AlgebraicGeometry.GroupoidScheme.sourceUnitIso_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.sourceUnitIso G).hom =
        AlgebraicGeometry.GroupoidScheme.sourceUnitMap G)

#check
  (AlgebraicGeometry.GroupoidScheme.differenceIso :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      AlgebraicGeometry.GroupoidScheme.relationSelfPullback G ≅
        AlgebraicGeometry.GroupoidScheme.stabilizerFiber G)

#check
  (AlgebraicGeometry.GroupoidScheme.differenceIso_hom :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      (AlgebraicGeometry.GroupoidScheme.differenceIso G).hom =
        AlgebraicGeometry.GroupoidScheme.differenceMap G)

#check
  (AlgebraicGeometry.GroupoidScheme.unitSquare_isPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      IsPullback (AlgebraicGeometry.GroupoidScheme.sourceProjection G)
        (AlgebraicGeometry.GroupoidScheme.unitBaseChangeMap G)
        (AlgebraicGeometry.GroupoidScheme.stabilizerOneLift G)
        (AlgebraicGeometry.GroupoidScheme.stabilizerProjection G))
