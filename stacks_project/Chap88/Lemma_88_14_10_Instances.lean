/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RestrictedPowerSeries.Adic

/-!
# Adic and Noetherian instances for restricted power series

Restricted power series in finitely many variables over a Noetherian adic ring
remain Noetherian and adic, so primes of `A{x₁, …, xₙ}` may carry `IsRigClosed`.
-/

@[expose] public section

universe u

#check (RestrictedPowerSeries.instIsAdicRing :
  ∀ (n : ℕ) {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A],
    TopologicalRing.IsAdicRing (RestrictedPowerSeries (Fin n) A))

#check (RestrictedPowerSeries.instIsNoetherianRing :
  ∀ (n : ℕ) {A : Type u} [CommRing A] [TopologicalSpace A]
    [TopologicalRing.IsAdicRing A] [IsNoetherianRing A],
    IsNoetherianRing (RestrictedPowerSeries (Fin n) A))
