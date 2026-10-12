/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Homotopy.Cofiber
import StacksCheckRecall

/-!
# Removing the final Koszul generator

@stack 0629
-/

@[expose] public section

/- Lemma 15.28.8: a finite-family Koszul complex is the homotopy cofiber of multiplication by
its final member on the complex of the truncated family. -/
@[stacks 0629 "Lemma 15.28.8"]
#check @KoszulComplex.Family.truncateLastIsoCofiber

#check @KoszulComplex.Family.snocLinearEquiv
#check @KoszulComplex.Family.snocCoprodIso
