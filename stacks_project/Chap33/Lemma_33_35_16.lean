module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial

@[expose] public section

universe u

/- Lemma 33.35.16: Let `k` be a field, let `n : ℕ`, let `ℱ` be a coherent sheaf on
standard projective `n`-space over `k`, and let `P : Polynomial ℚ` be its Hilbert polynomial.
Then for all sufficiently large integers `d`, `P(d)` equals the dimension of the zeroth
cohomology of the canonical twist `ℱ(d)`. -/
@[stacks 08AE]
#check (AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial.eventually_eq_finrank_cohomologyZero :
  ∀ (k : Type u) [Field k] (n : ℕ)
    (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent]
    (P : Polynomial ℚ),
    AlgebraicGeometry.ProjectiveSpace.IsHilbertPolynomial k n ℱ P →
      ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
        P.eval (d : ℚ) =
          (AlgebraicGeometry.Scheme.Hom.cohomologyFinrank
            (AlgebraicGeometry.ProjectiveSpace.toSpec k n)
            (AlgebraicGeometry.ProjectiveSpace.twist k n ℱ d) 0 : ℚ))
