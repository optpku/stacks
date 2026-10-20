/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.IntegralClosure.Complete

@[expose] public section

/-!
# Normal Formal Power Series Rings

This module relates normality of formal power series rings to normality and
complete normality of their coefficient rings.
-/

open scoped PowerSeries

universe u v

namespace PowerSeries

/-- A one-variable formal power series ring over a Noetherian integrally closed
domain is integrally closed. -/
@[stacks 0BI0]
instance instIsIntegrallyClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed R⟦X⟧ := sorry

/-- If the formal power series ring over a domain is flat over its polynomial
ring, then the domain is integrally closed exactly when its complete integral
closure in its fraction field is the base ring. -/
theorem isIntegrallyClosed_iff_completeIntegralClosure_eq_bot
    {R : Type u} {K : Type v} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (h_flat : Module.Flat (Polynomial R) (PowerSeries R)) :
    IsIntegrallyClosed R ↔ completeIntegralClosure R K = ⊥ := sorry

end PowerSeries
