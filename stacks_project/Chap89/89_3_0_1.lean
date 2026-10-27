/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.Excision

/-! # The excision functor at a finite family of closed points -/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u v

/- 0BHA::statement_repair::1 (spaces-resolve-equation-equivalence).
Base change along affine elementary étale neighbourhoods of pairwise distinct closed
points of a decent algebraic space defines a functor from morphisms that are
isomorphisms away from the selected finite family to families of morphisms that are
isomorphisms away from the distinguished neighbourhood points. The neighbourhoods
are shrunk so that the inverse image of the entire selected family is a singleton. -/
@[stacks 0BHA] #check (AlgebraicGeometry.AlgebraicSpace.excisionFamilyFunctor :
  ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U),
    IsoOverClosedPoints X x hx ⥤
      ∀ i, IsoOverOpen (closedPointComplementι (ofOver ((U i).toOver))
        (isClosed_neighborhoodPoint X x hx U hU i)))

#check (AlgebraicGeometry.AlgebraicSpace.excisionFamilyFunctor_eq :
  ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U)
    (Y : IsoOverClosedPoints X x hx) (i : ι),
    ((excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).obj Y i).obj =
      ((IsoOverClosedPoints.baseChangeFamily X x hx U).obj Y i).obj)
