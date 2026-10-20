/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Polynomial

/-!
# I-adic restricted power series

The canonical coefficient-stage algebra maps are owned by the polynomial adic-completion
module. This bridge preserves access for restricted-power-series consumers.
-/

@[expose] public section

universe u v

variable {A : Type u} [CommRing A] (σ : Type v) (I : Ideal A)

/- The canonical coefficient-stage algebra map for an arbitrary variable type. -/
#check (IAdicRestrictedPowerSeries.stageHom σ I :
  (n : ℕ) → IAdicRestrictedPowerSeries σ I →ₐ[A] MvPolynomial σ (A ⧸ I ^ n))
