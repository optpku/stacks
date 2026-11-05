/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Finite-variable power-series extensions of a specified ring map

The property records the coefficient inclusion, without choosing scalar actions,
residue-field identifications, or an isomorphism witnessing the property.
-/

@[expose] public section

universe u v

namespace RingHom

variable {Coeff : Type u} {Extension : Type v} [CommRing Coeff] [CommRing Extension]

/-- A specified ring map is a finite-variable power-series coefficient inclusion
up to a ring isomorphism of its target. -/
def IsPowerSeriesExtension (map : Coeff →+* Extension) : Prop :=
  ∃ numVars : ℕ, ∃ equiv : Extension ≃+* MvPowerSeries (Fin numVars) Coeff,
    equiv.toRingHom.comp map = MvPowerSeries.C

/-- An explicit isomorphism over the coefficient inclusion witnesses the property. -/
theorem IsPowerSeriesExtension.of_equiv {map : Coeff →+* Extension} {numVars : ℕ}
    (equiv : Extension ≃+* MvPowerSeries (Fin numVars) Coeff)
    (compat : equiv.toRingHom.comp map = MvPowerSeries.C) : IsPowerSeriesExtension map :=
  ⟨numVars, equiv, compat⟩

/-- The coefficient inclusion itself is a finite-variable power-series extension. -/
theorem isPowerSeriesExtension_C (numVars : ℕ) :
    IsPowerSeriesExtension
      (MvPowerSeries.C : Coeff →+* MvPowerSeries (Fin numVars) Coeff) :=
  ⟨numVars, RingEquiv.refl _, rfl⟩

end RingHom
