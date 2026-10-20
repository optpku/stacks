/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Kaehler.DeRham.DividedPowers

@[expose] public section

universe u v

export KaehlerDifferential.DeRham (dividedPowerRelations dividedPowerDifferential
  dividedPowerDifferentialForm dividedPowerDifferentialDerivation mem_dividedPowerRelations
  dividedPowerDifferentialDerivation_apply dividedPowerDifferentialForm_zero)

/- The divided-power differential quotient and its exterior powers. -/
#check (KaehlerDifferential.DeRham.dividedPowerDifferential :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B],
    (A →+* B) → ∀ {J : Ideal B}, DividedPowers J → Type v)

#check (KaehlerDifferential.DeRham.dividedPowerDifferentialForm :
  ∀ {A : Type u} [CommRing A] {B : Type v} [CommRing B],
    (A →+* B) → ∀ {J : Ideal B}, DividedPowers J → ℕ → Type v)
