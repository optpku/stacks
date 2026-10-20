/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.Unobstructed
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

/- Lemma 93.16.4: A separated finite-type local complete-intersection scheme over
`k`, of dimension at most one and smooth except at finitely many points, has an
unobstructed deformation category. -/
@[stacks 0DZQ] #check (FlatSchemeCat.isUnobstructed_deformationCategory :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (X : Scheme.{u}) (hX : X ⟶ Spec (CommRingCat.of k))
    [Scheme.Hom.FiniteType hX] [IsSeparated hX] [Syntomic hX]
    (hdim : topologicalKrullDim X ≤ 1)
    (hns : {x : X | ¬ Scheme.Hom.SmoothAt hX x}.Finite),
    Functor.IsUnobstructed (FlatSchemeCat.deformationForget Λ k X hX))
