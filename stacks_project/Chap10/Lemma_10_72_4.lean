module

public import ReasLib.RingTheory.Depth.SupportDim
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.72.4

@stack 0AUJ
-/

/- Lemma 10.72.4: ideal depth is finite when the ideal does not generate the
whole finite module. -/
@[stacks 0AUJ]
#check @Ideal.depth_lt_top_of_smul_top_ne_top
