module

public import ReasLib.RingTheory.Completion.Dimension
import StacksCheckRecall

/-!
# Lemma 15.43.1 (07NV)

@stack 07NV
-/

@[expose] public section

/- Lemma 15.43.1 (07NV): Krull dimension is preserved by maximal-ideal completion. -/
@[stacks 07NV]
#check @AdicCompletion.ringKrullDim_eq
