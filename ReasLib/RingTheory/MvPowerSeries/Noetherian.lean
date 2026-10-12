/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Noetherian multivariate power series rings

@stack 0306

This leaf owns the finite-variable Noetherian instance for `MvPowerSeries`.  The finite-variable
presentation is not part of the public statement; consumers use the typeclass directly.
-/

universe u v

namespace MvPowerSeries

variable {R : Type u} [CommRing R]

/-- A multivariate power series ring in finitely many variables over a Noetherian ring is
Noetherian. -/
@[stacks 0306]
instance instIsNoetherianRing {σ : Type v} [Finite σ] [IsNoetherianRing R] :
    IsNoetherianRing (MvPowerSeries σ R) := sorry

end MvPowerSeries
