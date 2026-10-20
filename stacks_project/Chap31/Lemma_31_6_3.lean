/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.Pushforward
import StacksCheckRecall

universe u

/- Lemma 31.6.3: for a finite morphism of schemes `f : X ⟶ S` and a quasicoherent module `ℱ`
on `X`, the weakly associated points of the pushforward are exactly the images under `f` of the
weakly associated points of `ℱ`. -/
@[stacks 05EZ] #check
  (AlgebraicGeometry.Scheme.Modules.weakAss_pushforward_eq_image_of_isFinite :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ).weakAss =
        f.base '' ℱ.weakAss)
