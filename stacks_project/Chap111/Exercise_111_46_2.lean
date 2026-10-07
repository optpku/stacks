module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap111.Exercise_111_46_2_Coincidence

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Exercise 111.46.2: let `k` be an algebraically closed field, let `X` be a smooth
curve over `k`, and let `1 ≤ r`. The closed subset
`D ⊂ X ⊗ tensorPower X r = tensorPower X (r + 1)` whose closed points are the tuples
`(x, x₁, …, x_r)` with `x = x_i` for some `i` has invertible ideal sheaf; in other
words, `D` is an effective Cartier divisor. -/
@[stacks 0EGA]
theorem isEffectiveCartierDivisor_coincidenceDivisor
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] (r : ℕ) (hr : 1 ≤ r) :
    IsEffectiveCartierDivisor (coincidenceDivisor X r).subschemeι :=
  sorry

end AlgebraicGeometry.SchemeOverField
