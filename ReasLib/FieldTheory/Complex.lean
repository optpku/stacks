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
