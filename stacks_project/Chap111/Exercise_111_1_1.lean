/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.Localization
import StacksCheckRecall

@[expose] public section

universe u

namespace Polynomial

/- Exercise 111.1.1: For a maximal ideal `m` of a commutative ring `A`, the
localizations of `A[X]` at `(m, X)` and `(m, X - 1)` are isomorphic.
These are `Polynomial.evaluationIdeal m 0` and `Polynomial.evaluationIdeal m 1`,
so the exercise is the case `a = 0` and `b = 1` of the following theorem. -/
@[stacks 02CG]
#check (Polynomial.nonempty_localizationAt_evaluationIdeal :
  ∀ {A : Type u} [CommRing A] (m : Ideal A) (a b : A) [m.IsMaximal],
    Nonempty (Localization.AtPrime (Polynomial.evaluationIdeal m a) ≃+*
      Localization.AtPrime (Polynomial.evaluationIdeal m b)))

end Polynomial
