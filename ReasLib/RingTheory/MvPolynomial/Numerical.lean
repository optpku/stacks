module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.ENat.Lattice

/-!
# Multivariable numerical polynomials

This file records a bottom-valued total degree for multivariate polynomials and a predicate for
integer-valued functions represented on all integer points by a rational multivariate polynomial
of bounded total degree.
-/

@[expose] public section

noncomputable section

universe u v

namespace MvPolynomial

variable {σ : Type u} {R : Type v} [CommSemiring R]

/-- The total degree of a multivariate polynomial, with the zero polynomial assigned degree
`⊥` and every nonzero polynomial assigned its ordinary total degree. -/
noncomputable def totalDegreeWithBotENat (P : MvPolynomial σ R) : WithBot ℕ∞ := by
  classical
  exact if P = 0 then ⊥ else ((P.totalDegree : ℕ∞) : WithBot ℕ∞)

end MvPolynomial

/-- An integer-valued function on integer points is a multivariable numerical polynomial of total
degree at most `d` if a rational multivariate polynomial agrees with it at every integer point and
has bottom-valued total degree at most `d`. -/
def IsMvNumericalPolynomialOfTotalDegreeLE {σ : Type u}
    (g : (σ → ℤ) → ℤ) (d : WithBot ℕ∞) : Prop :=
  ∃ P : MvPolynomial σ ℚ,
    P.totalDegreeWithBotENat ≤ d ∧
      ∀ n : σ → ℤ,
        MvPolynomial.eval (fun j : σ ↦ (n j : ℚ)) P = (g n : ℚ)
