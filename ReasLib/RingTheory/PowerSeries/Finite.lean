/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite Power-Series Extensions

This module records finiteness of the coefficientwise extension of formal
power-series rings.
-/

universe u v

open scoped PowerSeries

namespace Module.Finite

/-- A finite coefficient algebra induces a finite algebra of one-variable
formal power series. -/
theorem powerSeries {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    [Algebra R S] [Module.Finite R S] : Module.Finite R⟦X⟧ S⟦X⟧ := sorry

end Module.Finite
