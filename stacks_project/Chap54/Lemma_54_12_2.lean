/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.MvPolynomial.QuadraticIdeal
import StacksCheckRecall

@[expose] public section

open MvPolynomial

universe u

/- Lemma 54.12.2: if a nonzero quadratic polynomial in `κ[x, y]` belongs to the
square of an ideal of colength greater than one, then it is a scalar multiple of
the square of an affine-linear polynomial. -/
@[stacks 0BGD] #check (MvPolynomial.quadratic_eq_scalar_mul_sq_of_mem_ideal_sq :
    ∀ {κ : Type u} [Field κ] (I : Ideal (MvPolynomial (Fin 2) κ))
      (a b c d e f : κ),
    (¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0)) →
    (C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
        C e * X 0 * X 1 + C f * X 1 ^ 2 ∈ I ^ 2)
      → (1 < Module.rank κ (MvPolynomial (Fin 2) κ ⧸ I)) →
    ∃ j g h i : κ,
      C a + C b * X 0 + C c * X 1 + C d * X 0 ^ 2 +
          C e * X 0 * X 1 + C f * X 1 ^ 2 =
        C j * (C g + C h * X 0 + C i * X 1) ^ 2)
