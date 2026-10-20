/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import ReasLib.RingTheory.Module.Support.FiniteLength
public import ReasLib.RingTheory.Depth

@[expose] public section

universe u v

open IsLocalRing
open scoped ENat

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Every submodule of a finite module over a Noetherian local ring that is zero or
has support equal to the singleton closed point lies in the maximal-ideal primary component. -/
theorem le_primaryComponent_of_eq_bot_or_support_eq_closedPoint
    (N : Submodule R M) (hN : N = ⊥ ∨ Module.support R N = {closedPoint R}) :
    N ≤ (maximalIdeal R).primaryComponent M := sorry

/-- The maximal-ideal primary component of a finite module over a Noetherian local
ring is zero or has support equal to the singleton closed point. -/
theorem primaryComponent_eq_bot_or_support_eq_closedPoint :
    (maximalIdeal R).primaryComponent M = ⊥ ∨
      Module.support R ((maximalIdeal R).primaryComponent M) = {closedPoint R} := sorry

/-- The maximal-ideal primary component of a finite module over a Noetherian local
ring has finite length. -/
theorem length_primaryComponent_lt_top :
    Module.length R ((maximalIdeal R).primaryComponent M) < ⊤ := sorry

/-- The quotient of a finite module over a Noetherian local ring by its
maximal-ideal primary component has depth at least one. -/
theorem moduleDepth_quotient_primaryComponent_ge_one :
    (1 : ℕ∞) ≤ moduleDepth R (M ⧸ (maximalIdeal R).primaryComponent M) := sorry

end Module
