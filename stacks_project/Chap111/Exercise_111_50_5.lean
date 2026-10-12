/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.Jacobian
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open MvPolynomial

/- Exercise 111.50.5 (1): full Jacobian row rank at the origin implies regularity. -/
@[stacks 0D1T] #check (MvPolynomial.isRegularLocalRing_of_jacobianRank :
  ∀ {k : Type u} [Field k] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (h0 : ∀ j, eval (0 : Fin n → k) (f j) = 0),
    (jacobianAtOrigin f).rank = c →
      IsRegularLocalRing (Localization.AtPrime (originIdeal k n f)
        (hp := (originIdeal_isMaximal f h0).isPrime)))

/- Exercise 111.50.5 (2): the local dimension under the rank hypothesis is `n - c`. -/
@[stacks 0D1T] #check (MvPolynomial.ringKrullDim_eq_of_jacobianRank :
  ∀ {k : Type u} [Field k] {n c : ℕ} (f : Fin c → MvPolynomial (Fin n) k)
    (h0 : ∀ j, eval (0 : Fin n → k) (f j) = 0),
    (jacobianAtOrigin f).rank = c →
      ringKrullDim (Localization.AtPrime (originIdeal k n f)
        (hp := (originIdeal_isMaximal f h0).isPrime)) = n - c)

/- Exercise 111.50.5 (3): the repeated-relation quotient is regular at the origin. -/
@[stacks 0D1T] #check (MvPolynomial.redundant_isRegularLocalRing :
  ∀ (k : Type u) [Field k],
    IsRegularLocalRing (Localization.AtPrime (originIdeal k 2 (redundantRelations k))
      (hp := (redundantOriginIdeal_isMaximal k).isPrime)))

/- Exercise 111.50.5 (4): the repeated relations have Jacobian rank less than two. -/
@[stacks 0D1T] #check (MvPolynomial.redundant_jacobianRank_lt :
  ∀ (k : Type u) [Field k], (jacobianAtOrigin (redundantRelations k)).rank < 2)

/- Exercise 111.50.5 (5): the repeated-relation quotient has local dimension one. -/
@[stacks 0D1T] #check (MvPolynomial.redundant_ringKrullDim :
  ∀ (k : Type u) [Field k],
    ringKrullDim (Localization.AtPrime (originIdeal k 2 (redundantRelations k))
      (hp := (redundantOriginIdeal_isMaximal k).isPrime)) = 1)
