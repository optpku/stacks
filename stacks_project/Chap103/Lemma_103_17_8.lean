/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_17_8_Coh
public import stacks_project.Chap103.Lemma_103_17_8_Equivalence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory

/- Lemma 103.17.8: In the situation discussed above, the equivalence
QCoh(𝒪_X) ≅ QCoh(U, R, s, t, c) sends coherent sheaves to coherent sheaves and
vice versa, i.e., induces an equivalence Coh(𝒪_X) ≅ Coh(U, R, s, t, c). -/
@[stacks 0GRC]
#check AlgebraicStack.Coh.groupoidEquivalence
