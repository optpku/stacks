module

public import stacks_project.Chap111.Exercise_111_47_2_Family
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- Exercise 111.47.2: over an algebraically closed field `k` and for `2 ≤ g`, the
naive number of moduli of smooth projective hyperelliptic curves of genus `g` is
`2 * g - 1`. -/
@[stacks 0EGQ]
theorem hyperellipticNumberOfModuli_eq {k : Type u} [Field k] [IsAlgClosed k]
    {g : ℕ} (hg : 2 ≤ g) :
    hyperellipticNumberOfModuli k g = 2 * g - 1 :=
  sorry

end AlgebraicGeometry.Curve
