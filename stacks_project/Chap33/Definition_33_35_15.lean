module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial

@[expose] public section

universe u

/- Definition 33.35.15: for a field `k`, `n : ℕ`, and a coherent sheaf `ℱ` on standard
projective `n`-space over `k`, its Hilbert polynomial is the function
`d ↦ χ(ProjectiveSpace.scheme k n, ProjectiveSpace.twist k n ℱ d)`. -/
@[stacks 08AD] #check
  (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent],
      ℤ → ℤ)
