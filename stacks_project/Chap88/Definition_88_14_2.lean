/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Lemma_88_14_1_RigClosed
import StacksCheckRecall

@[expose] public section

/- Definition 88.14.2: let `A` be a Noetherian adic topological ring. Let `q ⊂ A`
be a prime ideal. We say `q` is rig-closed if the equivalent conditions of
Lemma 88.14.1 are satisfied. -/
@[stacks 0GG9] #check @Ideal.IsRigClosed
