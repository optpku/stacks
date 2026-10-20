/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.PowerSeries.Inverse
public import ReasLib.RingTheory.Depth

@[expose] public section

universe u

open scoped ENat

namespace PowerSeries

/-- The self-module of a one-variable power-series ring over a field has depth one. -/
theorem moduleDepth_self_eq_one (k : Type u) [Field k] :
    moduleDepth (PowerSeries k) (PowerSeries k) = 1 :=
  sorry

end PowerSeries
