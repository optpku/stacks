module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Normal Formal Power Series Rings

This module supplies the normality permanence property for one-variable formal
power series over Noetherian normal domains.

@stack 0BI0
-/

open scoped PowerSeries

universe u

namespace PowerSeries

/-- Lemma 10.37.9, tag `0BI0`: a one-variable formal power series ring over a
Noetherian integrally closed domain is integrally closed. -/
@[stacks 0BI0]
instance instIsIntegrallyClosed
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed R⟦X⟧ := sorry

end PowerSeries
