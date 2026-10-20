/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Descent
import StacksCheckRecall

universe u v

/- Lemma 36.12.3: for an fppf covering `𝒰` of a scheme `X`, a derived
`𝒪_X`-module `E` is `m`-pseudo-coherent if and only if every derived pullback
`L(𝒰.f i)^* E` is `m`-pseudo-coherent. -/
@[stacks 09UF] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isMPseudoCoherent_iff_fppfCover :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      (𝒰 : AlgebraicGeometry.FppfCover.{u, v} X)
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) (m : ℤ),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent E m ↔
        ∀ i : 𝒰.I₀, AlgebraicGeometry.RingedSpace.ModuleDerived.IsMPseudoCoherent
          ((AlgebraicGeometry.RingedSpace.modulePullbackDerived
            (𝒰.f i).toLRSHom.toShHom).obj E) m)
