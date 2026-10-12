/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Homotopy.Cofiber
import StacksCheckRecall

/-!
# The finite-family Koszul cofiber comparison

@stack 062C
-/

@[expose] public section

/- Lemma 15.28.11: replacing the final member of a finite family by `f * g` gives a Koszul
complex homotopy equivalent to the corresponding cofiber from the shifted `f`-family complex. -/
@[stacks 062C "Lemma 15.28.11"]
#check @KoszulComplex.Family.snocMul_exists_homotopyEquiv

#check @KoszulComplex.coprodScalarMul_exists_homotopyEquiv
