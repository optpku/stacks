/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Lemma_93_14_1_Henselization
import StacksCheckRecall

/-!
# Flat algebra lifts versus pair henselization
-/

@[expose] public section

/- Lemma 93.14.1: for a surjection `A' → A` of Noetherian rings with nilpotent
kernel, a finite-type flat `A`-algebra `B`, and an ideal `b ⊆ B` such that
`Spec(B) ⟶ Spec(A)` is syntomic on the complement of `V(b)`, `B` has a flat
lift to `A'` if and only if the pair henselization
`henselizationRing (pairOfIdeal b)` has a flat lift to `A'`. -/
@[stacks 0DZB]
#check @Algebra.NilpotentLift.existsFlatLift_iff_existsFlatLift_henselization

end
