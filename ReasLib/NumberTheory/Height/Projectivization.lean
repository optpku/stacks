/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization

universe u

@[expose] public section

namespace Projectivization

/-- The usual logarithmic height on rational projective space. -/
noncomputable def rationalLogHeight (n : ℕ)
    (p : Projectivization ℚ (Fin (n + 1) → ℚ)) : ℝ := logHeight p

end Projectivization
