/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Lemma_93_12_3_Lift
import StacksCheckRecall

/-!
# Flat algebra lifts versus adic completion
-/

@[expose] public section

/- Lemma 93.12.3: for a surjection `A' → A` of Noetherian rings with nilpotent
kernel, a finite-type flat `A`-algebra `B`, and an ideal `b ⊆ B` such that
`Spec(B) ⟶ Spec(A)` is syntomic on the complement of `V(b)`, `B` has a flat
lift to `A'` if and only if the `b`-adic completion `AdicCompletion b B` has a
flat lift to `A'`. -/
@[stacks 0DZ3]
#check @Algebra.NilpotentLift.existsFlatLift_iff_existsFlatLift_adicCompletion

end
