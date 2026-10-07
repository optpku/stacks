module

public import stacks_project.Chap93.Lemma_93_13_1_Localization
import StacksCheckRecall

/-!
# Flat algebra lifts versus localization
-/

@[expose] public section

/- Lemma 93.13.1: for a surjection `A' → A` of Noetherian rings with nilpotent
kernel, a finite-type flat `A`-algebra `B`, and a multiplicative subset
`S ⊆ B` such that if `Spec(B) ⟶ Spec(A)` is not syntomic at `q` then
`S ∩ q = ∅`, `B` has a flat lift to `A'` if and only if `Localization S`
has a flat lift to `A'`. -/
@[stacks 0DZ7]
#check @Algebra.NilpotentLift.existsFlatLift_iff_existsFlatLift_localization

end
