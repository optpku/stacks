/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPolynomial.XSqXY
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.10.2: a Noetherian ring with a prime ideal whose squared quotient
has an additional associated prime. -/
@[stacks 0CR9] #check (MvPolynomial.XSqXY.associatedPrimesOfModule_quot_spanX_sq :
  ∀ (k : Type u) [Field k],
    IsNoetherianRing (MvPolynomial.XSqXY.Quot k) ∧
      (MvPolynomial.XSqXY.spanX k).IsPrime ∧
      ({MvPolynomial.XSqXY.spanX k} ⊂ associatedPrimesOfModule
        (MvPolynomial.XSqXY.Quot k)
        (MvPolynomial.XSqXY.Quot k ⧸ MvPolynomial.XSqXY.spanX k ^ 2)))
