/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

@[expose] public section

universe u

namespace MvPolynomial

/-- A nonzero quadratic polynomial in two variables belonging to the square of an
ideal whose quotient has vector-space rank greater than one is a scalar multiple
of the square of an affine-linear polynomial. -/
theorem quadratic_eq_scalar_mul_sq_of_mem_ideal_sq
    {κ : Type u} [Field κ] (I : Ideal (MvPolynomial (Fin 2) κ))
    (a b c d e f : κ)
    (h_not_all_zero : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0))
    (h_mem : C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 ∈ I ^ 2)
    (h_colength : 1 < Module.rank κ (MvPolynomial (Fin 2) κ ⧸ I)) :
    ∃ j g h i : κ,
      C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
          C e * X 0 * X 1 + C f * X 1 ^ 2 =
        C j * (C g + C h * X 0 + C i * X 1) ^ 2 := sorry

end MvPolynomial
