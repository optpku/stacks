/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # The complex numbers as a quadratic extension of the real numbers -/

@[expose] public section

namespace Complex

/-- The complex numbers form a quadratic extension of the real numbers. -/
instance isQuadraticExtension : Algebra.IsQuadraticExtension ℝ ℂ where
  finrank_eq_two' := Complex.finrank_real_complex

end Complex
