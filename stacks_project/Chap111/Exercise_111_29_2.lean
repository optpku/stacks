/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.NumberTheory.PrimePolynomial
import StacksCheckRecall

@[expose]
public section

open scoped Polynomial

/- Exercise 111.29.2 (1): the explicit example `Polynomial.thirdCyclotomicY = Y ^ 2 + Y + 1`
has no root after specialization modulo infinitely many primes.
-/
@[stacks 02EP] #check
  (Polynomial.thirdCyclotomicY_evalXPowMod_not_isRoot_infinite :
    {p : ℕ | p.Prime ∧ ∀ a : ZMod p,
      ¬ (Polynomial.evalXPowMod p Polynomial.thirdCyclotomicY).IsRoot a}.Infinite)

/- Exercise 111.29.2 (2): the same example has a linear or quadratic factor after
specialization modulo every sufficiently large prime.
-/
@[stacks 02EP] #check
  (Polynomial.thirdCyclotomicY_evalXPowMod_linear_or_quadratic_factor_of_large :
    ∃ N : ℕ, ∀ p : ℕ, p.Prime → N ≤ p →
      ∃ q : (ZMod p)[X],
        (q.natDegree = 1 ∨ q.natDegree = 2) ∧
          q ∣ Polynomial.evalXPowMod p Polynomial.thirdCyclotomicY)
