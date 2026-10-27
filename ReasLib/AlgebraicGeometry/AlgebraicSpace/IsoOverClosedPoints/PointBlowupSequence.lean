/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.FinitePointSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.Excision

/-!
# Point-blowup factorizations and elementary étale excision

Finite point-blowup factorizations over a finite family of closed points can
be detected on affine elementary étale neighborhoods of those points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism that is an isomorphism away from finitely many distinct closed
points of a decent algebraic space factors into closed-point blowups over those
points if and only if its excision base changes factor into closed-point blowups
over the distinguished points of affine elementary étale neighborhoods. -/
theorem existsPointBlowupSequence_iff {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) (hx_inj : Function.Injective x)
    (U : ∀ i, EtaleNeighborhood X (x i)) (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary)
    (hU : supportedOnRange X x U) (Y : IsoOverClosedPoints X x hx) :
    FactorsAsPointBlowups Y.obj.hom (Set.range x) ↔
      ∀ i, FactorsAsPointBlowups
        (((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj.hom)
        {ofOver.pointsEquiv (U i).toOver (U i).point} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
