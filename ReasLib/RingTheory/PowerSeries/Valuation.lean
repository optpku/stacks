/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace PowerSeries

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]

/-- Formal power series over a valuation ring of Krull dimension greater than one are not
flat over its polynomial ring. -/
@[stacks 0F1Z]
theorem not_flat_polynomial (hdim : 1 < ringKrullDim R) :
    ¬ Module.Flat (Polynomial R) (PowerSeries R) := sorry

end PowerSeries
