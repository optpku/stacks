/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.EtaleRestriction

/-! # Tor dimension under restriction from the small Zariski site to the small étale site -/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

/-- A derived module sheaf on a scheme has Tor-amplitude in `[a, b]` if and only if
its canonical inverse image on the small étale site has Tor-amplitude in `[a, b]`. -/
theorem commSmallEtaleToZariski_hasTorAmplitudeIn_iff (X : Scheme.{u})
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      HasTorAmplitudeIn ((commSmallEtaleToZariskiDerived X).obj E) a b :=
  sorry

/-- A derived module sheaf on a scheme has finite Tor dimension if and only if
its canonical inverse image on the small étale site has finite Tor dimension. -/
theorem commSmallEtaleToZariski_hasFiniteTorDimension_iff (X : Scheme.{u})
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    HasFiniteTorDimension E ↔
      HasFiniteTorDimension ((commSmallEtaleToZariskiDerived X).obj E) :=
  sorry

end AlgebraicGeometry.Scheme.SiteRestriction
