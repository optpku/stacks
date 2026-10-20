/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Monic

@[expose] public section

open Polynomial
open scoped Polynomial

noncomputable section

universe u

namespace Polynomial.MonicDegreeEq

variable {A : Type u} [CommRing A]

/-- The leading-coefficient and degree-bound conditions for the polynomial `X ^ d - C a`. -/
theorem binomialMem (d : ℕ+) (a : A) :
    (X ^ (d : ℕ) - C a).coeff d = 1 ∧
      ∀ i > (d : ℕ), (X ^ (d : ℕ) - C a).coeff i = 0 := by
  constructor
  · simp [coeff_sub, coeff_X_pow, coeff_C, ne_of_gt d.pos]
  · intro i hi
    simp [coeff_sub, coeff_X_pow, coeff_C, ne_of_gt hi,
      ne_of_gt (lt_trans d.pos hi)]

/-- The monic polynomial `X ^ d - C a`, bundled with its positive degree `d`. -/
def binomial (d : ℕ+) (a : A) : MonicDegreeEq A d :=
  ⟨X ^ (d : ℕ) - C a, binomialMem d a⟩

/-- The polynomial underlying `binomial d a` is `X ^ d - C a`. -/
theorem coe_binomial (d : ℕ+) (a : A) :
    (binomial d a : A[X]) = X ^ (d : ℕ) - C a := rfl

end Polynomial.MonicDegreeEq

