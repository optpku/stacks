module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/- Exercise 111.45.2 (1): In Situation 111.45.1, if `P(t)` is the Hilbert polynomial of
`ℱ`, then the Hilbert polynomial of `ℱ(-13)` is `t ↦ P(t - 13)`. -/
@[stacks 0DCF] #check (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_twist_neg_thirteen :
    ∀ (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (t : ℤ),
      hilbertPolynomial k n (twist k n ℱ (-13)) t = hilbertPolynomial k n ℱ (t - 13))

/- Exercise 111.45.2 (2): In Situation 111.45.1, if `P₁` and `P₂` are the Hilbert
polynomials of `ℱ₁` and `ℱ₂`, then the Hilbert polynomial of `ℱ₁ ⊕ ℱ₂` is `P₁ + P₂`. -/
@[stacks 0DCF] #check (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_biprod :
    ∀ (k : Type u) [Field k] (n : ℕ)
      (ℱ₁ ℱ₂ : (scheme k n).Modules) [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (t : ℤ),
      hilbertPolynomial k n (ℱ₁ ⊞ ℱ₂) t =
        hilbertPolynomial k n ℱ₁ t + hilbertPolynomial k n ℱ₂ t)

/- Exercise 111.45.2 (3): In Situation 111.45.1, if `P₁` and `P₂` are the Hilbert
polynomials of `ℱ₁` and `ℱ₂` and `ℱ` is the kernel of a surjective map `ℱ₁ ⟶ ℱ₂`,
then the Hilbert polynomial of `ℱ` is `P₁ - P₂`. -/
@[stacks 0DCF] #check (AlgebraicGeometry.ProjectiveSpace.hilbertPolynomial_kernel_of_epi :
    ∀ (k : Type u) [Field k] (n : ℕ) {ℱ₁ ℱ₂ : (scheme k n).Modules}
      [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (φ : ℱ₁ ⟶ ℱ₂) [Epi φ] (t : ℤ),
      hilbertPolynomial k n (kernel φ) t =
        hilbertPolynomial k n ℱ₁ t - hilbertPolynomial k n ℱ₂ t)

end AlgebraicGeometry.ProjectiveSpace
