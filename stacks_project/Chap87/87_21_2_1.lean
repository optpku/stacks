module

public import stacks_project.Chap87.«87_21_2_1_Completion»
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»
import StacksCheckRecall

@[expose] public section

/- 87.21.2.1: the commutative square A ⟶ (A')^∧, B ⟶ (B')^∧ with vertical maps
φ : B ⟶ A and φ' : (B')^∧ ⟶ (A')^∧ used in Situation 87.21.2, where A, B are
countably indexed weakly admissible rings, A → A' and B → B' are étale ring maps
(no topology on A', B'), (A')^∧ = lim A' ⧸ I A' over weak ideals of definition of A
(and likewise for B), and φ, φ' are continuous. -/
@[stacks 0ANC] #check TopologicalRing.LocalizeSquare

#check TopologicalRing.weakIdealCompletion
#check TopologicalRing.weakIdealCompletion.of
