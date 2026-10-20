/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- Lemma 75.6.1 (1): derived pushforward along a quasi-compact and quasi-separated
morphism of algebraic spaces preserves quasi-coherent cohomology. -/
@[stacks 08FA] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn.mapsTo :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f],
      derivedQuasiCoherentModuleProperty X ≤
        (derivedQuasiCoherentModuleProperty Y).inverseImage
          (Modules.moduleDerivedPushforward f))

/- Lemma 75.6.1 (2): over a quasi-compact base, derived pushforward along a
quasi-compact and quasi-separated morphism has a uniform upper cohomological bound on
objects whose positive cohomology vanishes. -/
@[stacks 08FA] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn.uniformUpperBound :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [IsQuasiCompact Y],
      ∃ N : ℤ, ∀ E : DerivedQCoh X,
        E.obj.IsLE 0 → ((pushforwardCohomologyIn f).obj E).obj.IsLE (N - 1))

/- Lemma 75.6.1 (3): the upper cohomological bound for derived pushforward can be
chosen uniformly after every base change. -/
@[stacks 08FA] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardCohomologyIn.baseChangeUpperBound :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f]
      [IsQuasiCompact Y],
      ∃ N : ℤ, ∀ ⦃Y' : AlgebraicSpace S⦄ (g : Y' ⟶ Y)
        (E : DerivedQCoh (pullback f g)),
        E.obj.IsLE 0 →
          ((pushforwardCohomologyIn (pullback.snd f g)).obj E).obj.IsLE (N - 1))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
