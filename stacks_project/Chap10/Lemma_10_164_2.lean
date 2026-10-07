module

public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.164.2

@stack 033F
-/

/- Lemma 10.164.2 [stacks 033F]: canonical recall of reducedness descent along
a faithfully flat ring homomorphism. -/
@[stacks 033F]
#check @RingHom.FaithfullyFlat.isReduced
