/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.CohomologicalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison

/-!
# Cohomological dimension of derived pushforward

This module records upper cohomological bounds for derived pushforward of complexes with
quasicoherent cohomology, including a bound uniform under arbitrary base change.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn

/-- Over a quasi-compact base, derived pushforward along a quasi-compact and quasi-separated
morphism has a uniform upper cohomological bound on complexes whose positive cohomology
vanishes. -/
theorem uniformUpperBound {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, ∀ E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace),
      E.obj.IsLE 0 →
        ((pushforwardCohomologyIn f).obj E).obj.IsLE (N - 1) := sorry

/-- The upper cohomological bound for derived pushforward along a quasi-compact and
quasi-separated morphism can be chosen uniformly after every base change. -/
theorem baseChangeUpperBound {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S)
      (E : DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (pullback f g).toRingedSpace)),
      E.obj.IsLE 0 →
        ((pushforwardCohomologyIn (pullback.snd f g)).obj E).obj.IsLE (N - 1) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn

end
