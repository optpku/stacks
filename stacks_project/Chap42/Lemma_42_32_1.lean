/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback.AffineBundle

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.32.1: if a flat morphism of relative dimension `r` is locally over its target
isomorphic to relative affine `r`-space, then its pullback on Chow groups is surjective. -/
@[stacks 02TT] #check
  (AlgebraicGeometry.ChowGroup.flatPullback_surjective_of_localAffineSpace :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (h_local : ∀ y : Y.left, ∃ U : Y.left.Opens, y ∈ U ∧
        Nonempty (Over.mk (f.left ∣_ U) ≅
          Over.mk (𝔸(ULift.{u} (Fin r); U.toScheme) ↘ U.toScheme)))
      (k : ℤ),
      Function.Surjective (AlgebraicGeometry.ChowGroup.flatPullback δ X Y f r k))
