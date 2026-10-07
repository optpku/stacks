module

public import stacks_project.Chap111.Exercise_111_45_3_Line
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.StandardLine

/-- Exercise 111.45.3: In Situation 111.45.1 assume `1 ≤ n`. The pushforward
`twistPushforward k n hn (-102)` of the restriction of `twistingSheaf k n (-102)`
along the standard coordinate line in `ProjectiveSpace.scheme k n` is a coherent
sheaf whose Hilbert polynomial is `fun t ↦ t - 101`. -/
@[stacks 0DCG]
theorem hilbertPolynomial_twistPushforward_neg102
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    hilbertPolynomial k n (twistPushforward k n hn (-102)) =
      fun t ↦ t - 101 := sorry

/-- The exhibited coherent sheaf has Hilbert polynomial
`Polynomial.X - Polynomial.C (101 : ℚ)`. -/
theorem isHilbertPolynomial_twistPushforward_neg102
    (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) :
    IsHilbertPolynomial k n (twistPushforward k n hn (-102))
      (Polynomial.X - Polynomial.C (101 : ℚ)) := sorry

end AlgebraicGeometry.ProjectiveSpace.StandardLine
