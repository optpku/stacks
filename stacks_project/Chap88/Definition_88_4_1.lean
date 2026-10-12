/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_18_1_Ring
import StacksCheckRecall

@[expose] public section

/- Definition 88.4.1: let `A` be a Noetherian ring and let `I ⊆ A` be an ideal.
Let `B` be an object of `C'` (`Algebra.TopologicallyFiniteType I B`: `B` is
`I`-adically complete and `B ⧸ I B` is of finite type over `A ⧸ I`). We say `B`
is rig-smooth over `(A, I)` if there exists an integer `c ≥ 0` such that
`I ^ c` annihilates `Ext¹_B(NL_{B/A}^∧, N)` for every `B`-module `N`. -/
@[stacks 0GAI] #check Algebra.RigSmooth
