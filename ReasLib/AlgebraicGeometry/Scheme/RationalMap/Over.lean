/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Birational.RationalMap

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.RationalMap

/-- A rational map is over a base scheme exactly when it has a partial-map representative
over that base. -/
theorem isOver_iff_exists_partialMap_over {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    (φ : X ⤏ Y) :
    φ.IsOver S ↔ ∃ f : X.PartialMap Y, f.IsOver S ∧ f.toRationalMap = φ := by
  constructor
  · intro h
    exact h.exists_partialMap_over
  · intro h
    exact ⟨h⟩

end AlgebraicGeometry.Scheme.RationalMap
