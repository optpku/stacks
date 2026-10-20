module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial.Existence
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.45.4: In Situation 111.45.1, if `2 ≤ n`, there exists a coherent
`𝒪`-module on projective space whose Hilbert polynomial is `t² / 2 + t / 2 - 1`. -/
@[stacks 0DCH] #check
  (AlgebraicGeometry.ProjectiveSpace.exists_isHilbertPolynomial_quadratic :
    ∀ (k : Type u) [Field k] (n : ℕ), 2 ≤ n →
      ∃ (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules)
        (hcoherent : ℱ.IsCoherent),
        AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial k n ℱ
          (Polynomial.C (1 / 2 : ℚ) * Polynomial.X ^ 2 +
            Polynomial.C (1 / 2 : ℚ) * Polynomial.X - 1))
