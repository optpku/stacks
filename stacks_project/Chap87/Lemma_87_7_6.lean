/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_7_6_Completed
import StacksCheckRecall

@[expose] public section

open Algebra.TensorProduct

/- Lemma 87.7.6: If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are weakly pre-adic, then
A ⊗̂_B C is weakly adic. -/
@[stacks 0GXJ] #check @Completed.isWeaklyAdicRing
