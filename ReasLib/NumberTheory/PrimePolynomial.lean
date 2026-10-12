/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Prime-indexed polynomial specializations

This file constructs the reduction of a bivariate integer polynomial after substituting
the second variable by a prime-indexed power of the first variable.
-/

@[expose]
public section

noncomputable section

open Polynomial
open scoped Polynomial Polynomial.Bivariate

namespace Polynomial

/-- The reduction `f_p` of a bivariate integer polynomial `f : ℤ[X][Y]`: substitute
`Y` by `X ^ p`, then reduce coefficients along `Int.castRingHom (ZMod p)`. -/
def evalXPowMod (p : ℕ) (f : ℤ[X][Y]) : (ZMod p)[X] :=
  (eval (X ^ p) f).map (Int.castRingHom (ZMod p))

/-- The prime-indexed specialization unfolds as bivariate evaluation followed by coefficient
reduction modulo `p`. -/
theorem evalXPowMod_eq (p : ℕ) (f : ℤ[X][Y]) :
    evalXPowMod p f = (eval (X ^ p) f).map (Int.castRingHom (ZMod p)) := sorry

/-- Pointwise evaluation of `evalXPowMod p f` is coefficient reduction of `f` followed by
`evalEval` at `(a, a ^ p)`. -/
theorem eval_evalXPowMod (p : ℕ) (f : ℤ[X][Y]) (a : ZMod p) :
    eval a (evalXPowMod p f) =
      (f.map (mapRingHom (Int.castRingHom (ZMod p)))).evalEval a (a ^ p) := sorry

/-- The roots of `evalXPowMod p f` are exactly the zeros of the coefficient-reduced bivariate
polynomial evaluated at `(a, a ^ p)`. -/
theorem isRoot_evalXPowMod_iff (p : ℕ) (f : ℤ[X][Y]) (a : ZMod p) :
    (evalXPowMod p f).IsRoot a ↔
      (f.map (mapRingHom (Int.castRingHom (ZMod p)))).evalEval a (a ^ p) = 0 := sorry

/-- For a prime `p`, roots of `evalXPowMod p f` are zeros of the coefficient-reduced bivariate
polynomial on the diagonal `(a, a)`. -/
theorem isRoot_evalXPowMod_iff_evalEval_self {p : ℕ} (hp : p.Prime) (f : ℤ[X][Y])
    (a : ZMod p) :
    (evalXPowMod p f).IsRoot a ↔
      (f.map (mapRingHom (Int.castRingHom (ZMod p)))).evalEval a a = 0 := sorry

/-- The bivariate polynomial `Y ^ 2 + Y + 1` in `ℤ[X][Y]`. -/
def thirdCyclotomicY : ℤ[X][Y] :=
  Y ^ 2 + Y + 1

/-- The prime-indexed specialization of `thirdCyclotomicY` is
`X ^ (2 * p) + X ^ p + 1`. -/
theorem evalXPowMod_thirdCyclotomicY (p : ℕ) :
    evalXPowMod p thirdCyclotomicY = X ^ (2 * p) + X ^ p + 1 := sorry

/-- Infinitely many prime-indexed specializations of `thirdCyclotomicY` have no root in their
coefficient field. -/
theorem thirdCyclotomicY_evalXPowMod_not_isRoot_infinite :
    {p : ℕ | p.Prime ∧ ∀ a : ZMod p, ¬ (evalXPowMod p thirdCyclotomicY).IsRoot a}.Infinite := sorry

/-- Beyond some natural threshold, every prime-indexed specialization of `thirdCyclotomicY`
has a divisor of natural degree one or two. -/
theorem thirdCyclotomicY_evalXPowMod_linear_or_quadratic_factor_of_large :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      ∃ q : (ZMod p)[X],
        (q.natDegree = 1 ∨ q.natDegree = 2) ∧ q ∣ evalXPowMod p thirdCyclotomicY := sorry

end Polynomial
