/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Finite

open scoped AlgebraicGeometry

universe u

/- Lemma 31.17.1: let `π : X ⟶ Y` be a finite morphism of schemes and let `ℒ` be an
invertible `𝒪_X`-module. For every point `y : Y`, there is an open neighborhood `V` of `y`
such that `ℒ` restricted to `π⁻¹(V)` is trivial. -/
@[stacks 0BUT] #check
  (AlgebraicGeometry.Scheme.exists_open_neighborhood_isTrivial_pullback_of_isFinite :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ Y) [AlgebraicGeometry.IsFinite π]
      (ℒ : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible ℒ] (y : Y),
      ∃ V : Y.Opens, y ∈ V ∧
        AlgebraicGeometry.RingedSpace.IsTrivial
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (X.ofRestrict (π ⁻¹ᵁ V).isOpenEmbedding)).obj ℒ))
