/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.ChangeOfBasis
import StacksCheckRecall

/-!
# Invertible changes of Koszul generators

@stack 0625
-/

@[expose] public section

/- Lemma 15.28.4: an invertible matrix of linear combinations induces an isomorphism of
the corresponding finite-family Koszul complexes. -/
@[stacks 0625 "Lemma 15.28.4"]
#check @KoszulComplex.matrixLinearCombinationIso

#check @KoszulComplex.linearForm_matrixTranspose
#check @KoszulComplex.linearForm_matrixTranspose_comp_inv
#check @KoszulComplex.matrixLinearCombinationIso_hom_f
