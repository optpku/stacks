/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Polynomial.Numerical.Difference
import StacksCheckRecall

/-!
@stack 00JZ
-/

@[expose] public section

/- Lemma 10.58.5 (Tag 00JZ): the predecessor-difference antiderivative criterion. -/
@[stacks 00JZ]
#check @IsNumericalPolynomial.of_sub_pred

@[stacks 00JZ "forward-difference criterion"]
#check @IsNumericalPolynomial.of_fwdDiff_one
