/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Biproduct
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Exercise 111.45.2 (1): In Situation 111.45.1, if `P(t)` is the Hilbert polynomial of
`ℱ`, then the Hilbert polynomial of `ℱ(-13)` is `t ↦ P(t - 13)`. -/
@[stacks 0DCF]
theorem hilbertPolynomial_twist_neg_thirteen
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (t : ℤ) :
    hilbertPolynomial k n (twist k n ℱ (-13)) t = hilbertPolynomial k n ℱ (t - 13) :=
  sorry

/-- The biproduct of coherent modules on standard projective space is coherent. -/
instance instIsCoherent_biprod {k : Type u} [Field k] {n : ℕ}
    (ℱ₁ ℱ₂ : (scheme k n).Modules) [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] :
    (ℱ₁ ⊞ ℱ₂).IsCoherent := sorry

/-- Exercise 111.45.2 (2): In Situation 111.45.1, if `P₁` and `P₂` are the Hilbert
polynomials of `ℱ₁` and `ℱ₂`, then the Hilbert polynomial of `ℱ₁ ⊕ ℱ₂` is `P₁ + P₂`. -/
@[stacks 0DCF]
theorem hilbertPolynomial_biprod
    (k : Type u) [Field k] (n : ℕ)
    (ℱ₁ ℱ₂ : (scheme k n).Modules) [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (t : ℤ) :
    hilbertPolynomial k n (ℱ₁ ⊞ ℱ₂) t =
      hilbertPolynomial k n ℱ₁ t + hilbertPolynomial k n ℱ₂ t :=
  sorry

/-- The kernel of a morphism of coherent modules on standard projective space is coherent. -/
instance instIsCoherent_kernel {k : Type u} [Field k] {n : ℕ}
    {ℱ₁ ℱ₂ : (scheme k n).Modules} [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (φ : ℱ₁ ⟶ ℱ₂) :
    (kernel φ).IsCoherent := sorry

/-- Exercise 111.45.2 (3): In Situation 111.45.1, if `P₁` and `P₂` are the Hilbert
polynomials of `ℱ₁` and `ℱ₂` and `ℱ` is the kernel of a surjective map `ℱ₁ ⟶ ℱ₂`,
then the Hilbert polynomial of `ℱ` is `P₁ - P₂`. -/
@[stacks 0DCF]
theorem hilbertPolynomial_kernel_of_epi
    (k : Type u) [Field k] (n : ℕ) {ℱ₁ ℱ₂ : (scheme k n).Modules}
    [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (φ : ℱ₁ ⟶ ℱ₂) [Epi φ] (t : ℤ) :
    hilbertPolynomial k n (kernel φ) t =
      hilbertPolynomial k n ℱ₁ t - hilbertPolynomial k n ℱ₂ t :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
