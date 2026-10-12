/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_18_1_Ring
import StacksCheckRecall

@[expose] public section

/- Definition 88.17.2: let `φ : A →+* B` be a continuous ring homomorphism
between adic Noetherian topological rings, i.e., `φ` is an arrow of
`WAdm^{Noeth}`. We say `φ` is rig-smooth if the equivalent conditions of
Lemma 88.17.1 hold. -/
@[stacks 0GCJ] #check RingHom.RigSmooth
