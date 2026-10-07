module

public import ReasLib.RingTheory.Smooth.Adic.Lifting
import StacksCheckRecall

/-!
# Lemma 15.37.5 (07NJ)

@stack 07NJ
-/

@[expose] public section

/- Lemma 15.37.5 (07NJ): an adically formally smooth map lifts continuously across the stated
closed ideal in a complete adic target. -/
@[stacks 07NJ "adic formal smoothness lifting theorem"]
#check @RingHom.exists_continuous_lift_of_formally_smooth_for_adic
