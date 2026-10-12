/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.DirectSum
import StacksCheckRecall

/-!
# Koszul complexes of concatenated families

@stack 0664
-/

@[expose] public section

/- Lemma 15.28.12: the Koszul complex on the concatenation of two finite families is the tensor
product of their Koszul complexes. -/
@[stacks 0664 "Lemma 15.28.12"]
#check @KoszulComplex.Family.appendIsoTensor

#check @KoszulComplex.DirectSum.isoTensor
#check @KoszulComplex.Family.appendLinearEquiv
#check @KoszulComplex.Family.appendCoprodIso
