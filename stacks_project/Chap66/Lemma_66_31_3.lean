/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.31.3: pullback along any morphism of algebraic spaces over a scheme preserves
local projectivity of quasi-coherent modules. -/
@[stacks 060S] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullback_isLocallyProjective :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective 𝒢],
      AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective
        ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj 𝒢))

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective.pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) {𝒢 : Y.Modules} [𝒢.IsQuasicoherent],
      AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective 𝒢 →
        AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective
          ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj 𝒢))
