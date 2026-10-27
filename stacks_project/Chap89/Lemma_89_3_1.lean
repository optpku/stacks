/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverClosedPoints.Excision

/-!
# Equivalence of the excision functor at a finite family of closed points

Base change along a finite family of affine elementary étale neighbourhoods of
pairwise distinct closed points of a decent algebraic space is an
equivalence of iso-over-open slice categories.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 89.3.1: let `S` be a scheme and `X` a decent algebraic space over
`S`. Let `x : ι → Points X` be a finite family of pairwise distinct closed
points, and let `U i` be affine elementary étale neighbourhoods of `x i`,
shrunk so that the inverse image of the selected finite range is exactly the
distinguished singleton. The functor of 89.3.0.1 is an equivalence of categories. -/
@[stacks 0BHB] #check (AlgebraicGeometry.AlgebraicSpace.excisionFamilyFunctor_isEquivalence :
  ∀ {ι : Type v} [Finite ι] {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X))
    (hx_inj : Function.Injective x) (U : ∀ i, EtaleNeighborhood X (x i))
    (hU_affine : ∀ i, IsAffine (U i).scheme)
    (hU_elem : ∀ i, (U i).IsElementary) (hU : supportedOnRange X x U),
    (excisionFamilyFunctor X x hx hx_inj U hU_affine hU_elem hU).IsEquivalence)
