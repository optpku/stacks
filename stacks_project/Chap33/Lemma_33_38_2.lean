/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.DimensionOne
import StacksCheckRecall

@[expose] public section

/- Lemma 33.38.2: an affine scheme whose local rings are Noetherian of dimension at most one has
affine quasi-compact opens. -/
@[stacks 09N9] #check
  (AlgebraicGeometry.Scheme.isAffineOpen_of_quasiCompact_of_stalk_ringKrullDim_le_one :
    ∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X]
      [∀ x : X, IsNoetherianRing (X.presheaf.stalk x)],
      (∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1) →
        ∀ (U : X.Opens) [AlgebraicGeometry.QuasiCompact U.ι],
          AlgebraicGeometry.IsAffineOpen U)
