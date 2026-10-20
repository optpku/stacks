/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Data.Complex.Basic

@[expose] public section

open scoped Cardinal RatFunc

universe u

namespace RatFunc

/-- The rational function field in one variable over `ℂ` has uncountable Hamel dimension over `ℂ`. -/
theorem aleph0_lt_rank_complex : ℵ₀ < Module.rank ℂ ℂ⟮X⟯ := sorry

end RatFunc
