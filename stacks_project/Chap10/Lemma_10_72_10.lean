module

public import ReasLib.RingTheory.Depth.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.72.10

@stack 0FCC
-/

-- Lemma 10.72.10 (0FCC): depth is bounded by localized depth plus quotient dimension.
@[stacks 0FCC]
#check @Module.moduleDepth_le_atPrime_add_quotientDim
