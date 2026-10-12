/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.«87_21_2_1_Completion»
public import stacks_project.Chap87.«87_21_2_1_LocalizeSquare»
import StacksCheckRecall

@[expose] public section

universe u

/- 87.21.2.1: the commutative square A ⟶ (A')^∧, B ⟶ (B')^∧ with vertical maps
φ : B ⟶ A and φ' : (B')^∧ ⟶ (A')^∧ used in Situation 87.21.2, where A, B are
countably indexed weakly admissible rings, A → A' and B → B' are étale ring maps
(no topology on A', B'), (A')^∧ = lim A' ⧸ I A' over weak ideals of definition of A
(and likewise for B), and φ, φ' are continuous. -/
@[stacks 0ANC] #check (TopologicalRing.LocalizeSquare :
  ∀ (A B A' B' : Type u)
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyAdmissibleRing A]
    [TopologicalRing.IsCountablyIndexed A]
    [CommRing B] [TopologicalSpace B] [TopologicalRing.IsWeaklyAdmissibleRing B]
    [TopologicalRing.IsCountablyIndexed B]
    [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    [CommRing B'] [Algebra B B'] [Algebra.Etale B B'], Type u)

#check TopologicalRing.weakIdealCompletion
#check TopologicalRing.weakIdealCompletion.of
