/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.PointBlowupSequence
import StacksCheckRecall

/-!
# Equivalence of point-blowup factorizations under family excision
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 89.4.2: Under elementary étale family excision, a morphism factors
into closed-point blowups over the selected closed points if and only if
each coordinate factors into closed-point blowups over its distinguished point. -/
@[stacks 0BHF] #check (AlgebraicGeometry.AlgebraicSpace.existsPointBlowupSequence_iff :
    ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) (hx_inj : Function.Injective x)
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary)
    (hU : supportedOnRange X x U) (Y : IsoOverClosedPoints X x hx),
    FactorsAsPointBlowups Y.obj.hom (Set.range x) ↔
      ∀ i, FactorsAsPointBlowups
        (((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj.hom)
        {ofOver.pointsEquiv (U i).toOver (U i).point})
