module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.HilbertPolynomial
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Limits

/-!
# Hilbert polynomials under twists, direct sums, and kernels

Integral twists translate Hilbert polynomials, binary direct sums add them, and kernels
of epimorphisms subtract them.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Twisting a coherent module on projective space by an integer translates its Hilbert
polynomial by that integer. -/
theorem hilbertPolynomial_twist
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (a t : ℤ) :
    hilbertPolynomial k n (twist k n ℱ a) t = hilbertPolynomial k n ℱ (t + a) :=
  sorry

/-- Twisting a coherent module on projective space by negative thirteen translates its
Hilbert polynomial by negative thirteen. -/
theorem hilbertPolynomial_twist_neg_thirteen
    (k : Type u) [Field k] (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (t : ℤ) :
    hilbertPolynomial k n (twist k n ℱ (-13)) t = hilbertPolynomial k n ℱ (t - 13) := by
  simpa only [sub_eq_add_neg] using hilbertPolynomial_twist k n ℱ (-13) t

/-- The Hilbert polynomial of a binary direct sum of coherent modules on projective space
is the sum of their Hilbert polynomials. -/
theorem hilbertPolynomial_biprod
    (k : Type u) [Field k] (n : ℕ)
    (ℱ₁ ℱ₂ : (scheme k n).Modules) [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (t : ℤ) :
    hilbertPolynomial k n (ℱ₁ ⊞ ℱ₂) t =
      hilbertPolynomial k n ℱ₁ t + hilbertPolynomial k n ℱ₂ t :=
  sorry

/-- The Hilbert polynomial of the kernel of an epimorphism between coherent modules on
projective space is the difference of their Hilbert polynomials. -/
theorem hilbertPolynomial_kernel_of_epi
    (k : Type u) [Field k] (n : ℕ) {ℱ₁ ℱ₂ : (scheme k n).Modules}
    [ℱ₁.IsCoherent] [ℱ₂.IsCoherent] (φ : ℱ₁ ⟶ ℱ₂) [Epi φ] (t : ℤ) :
    hilbertPolynomial k n (kernel φ) t =
      hilbertPolynomial k n ℱ₁ t - hilbertPolynomial k n ℱ₂ t :=
  sorry

end AlgebraicGeometry.ProjectiveSpace
