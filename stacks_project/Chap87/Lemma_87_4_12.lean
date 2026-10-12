/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_4_12_Completed
import StacksCheckRecall

@[expose] public section

open Algebra.TensorProduct

/- Lemma 87.4.12 (1): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are weakly pre-admissible, then
A ⊗̂_B C is weakly admissible. -/
@[stacks 0GB4] #check @Completed.isWeaklyAdmissibleRing

/- Lemma 87.4.12 (2): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are pre-admissible, then
A ⊗̂_B C is admissible. -/
@[stacks 0GB4] #check @Completed.isAdmissibleRing

/- Lemma 87.4.12 (3): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C have a countable fundamental system
of open ideals, then A ⊗̂_B C has a countable fundamental system of open
ideals. -/
@[stacks 0GB4] #check @Completed.isCountablyGenerated_nhds

/- Lemma 87.4.12 (4): If B → A and B → C are continuous homomorphisms of
linearly topologized rings and A and C are pre-adic with finitely generated
ideals of definition, then A ⊗̂_B C is adic and has a finitely generated
ideal of definition. -/
@[stacks 0GB4] #check @Completed.isAdicWithFGIdealOfDefinition

/- Lemma 87.4.12 (5): If B → A and B → C are continuous homomorphisms of
linearly topologized rings, A and C are pre-adic Noetherian rings, and
B ⧸ topologicalNilradical B →+* A ⧸ topologicalNilradical A is of finite
type, then A ⊗̂_B C is adic Noetherian. -/
@[stacks 0GB4] #check @Completed.isAdicNoetherianRing
