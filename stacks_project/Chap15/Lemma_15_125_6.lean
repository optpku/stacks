/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.SmithNormalForm
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.125.6

@stack 0ASS

The Bézout consequence is a canonical ReasLib instance.  This chapter entry
is intentionally a thin recall so later module and Smith-form arguments can
import the owner directly.
-/

/- Lemma 15.125.6: every elementary divisor domain is Bézout. -/
@[stacks 0ASS "Lemma 15.125.6, elementary divisor domains are Bezout"]
#check @isBezout_of_isElementaryDivisorDomain

#check @IsElementaryDivisorDomain.hasElementaryDivisorDiagonal
