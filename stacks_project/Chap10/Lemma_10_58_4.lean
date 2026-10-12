/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical.Closure
import StacksCheckRecall

/-!
# Lemma 10.58.4

@stack 00JY
-/

@[expose] public section

/- Lemma 10.58.4 (Tag 00JY): postcomposition of a numerical polynomial by an additive map. -/
@[stacks 00JY]
#check @IsNumericalPolynomial.comp
