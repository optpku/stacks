/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial powers in positive characteristic

This leaf records the characteristic-independent polynomial calculation used by
the Kähler and purely inseparable support APIs.  The statement is deliberately
parameterized by an arbitrary commutative ring with a `CharP` instance; a
particular prime field is only a specialization.

@stack 00TY
-/

@[expose] public section

universe u

namespace Polynomial

variable {R : Type u} [Semiring R]

/-- In characteristic `p`, the formal derivative of `X^p` is zero. -/
@[simp]
theorem derivative_X_pow_eq_zero {p : ℕ} [CharP R p] :
    Polynomial.derivative (Polynomial.X ^ p : Polynomial R) = 0 := by
  rw [Polynomial.derivative_X_pow]
  simp

end Polynomial
