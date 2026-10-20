/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleCounit
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma [Stacks 0HAP]: if `f : X ⟶ Y` is a quasi-compact separated étale morphism of
algebraic spaces, then for every quasi-coherent `𝒪_X`-module `ℱ` the adjunction counit
`(pullback f).obj ((pushforward f).obj ℱ) ⟶ ℱ` is split as an `𝒪_X`-linear map. -/
@[stacks 0HAP] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullbackPushforwardAdjunction.counit_isSplitEpi :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [Separated f] [Etale f] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      IsSplitEpi ((pullbackPushforwardAdjunction f).counit.app ℱ))

end AlgebraicGeometry.AlgebraicSpace.Modules
