/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CommRingedHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Module.Derived.EtaleRestriction

/-! # Relative Tor dimension under small étale restriction -/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.AssociatedModule
open RingedSite.Hom RingedSite.Hom.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

variable {X Y : Scheme.{u}}

/-- Relative Tor-amplitude in any fixed integer interval is preserved and reflected
by canonical inverse image from the small Zariski site to the small étale site. -/
theorem hasTorAmplitudeInOver_iff (f : X ⟶ Y)
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) (a b : ℤ) :
    HasTorAmplitudeInOver (zariskiCommRingedHom f) E a b ↔
      HasTorAmplitudeInOver (Scheme.Etale.Small.commRingedHom f)
        ((commSmallEtaleToZariskiDerived X).obj E) a b := sorry

/-- Covering-local finite relative Tor dimension is preserved and reflected
by canonical inverse image from the small Zariski site to the small étale site. -/
theorem locallyHasFiniteTorDimensionOver_iff (f : X ⟶ Y)
    (E : ModuleDerived.{u + 1} (smallCommRingedSite .zariski X)) :
    LocallyHasFiniteTorDimensionOver (zariskiCommRingedHom f) E ↔
      LocallyHasFiniteTorDimensionOver (Scheme.Etale.Small.commRingedHom f)
        ((commSmallEtaleToZariskiDerived X).obj E) := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
