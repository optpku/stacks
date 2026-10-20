module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective
import StacksCheckRecall

/-!
# Lemma 10.93.1

@stack 059X
-/

@[expose] public section

/- Chap10 Lemma 10 93 1: a countably generated flat Mittag-Leffler module is projective. -/
@[stacks 059X]
#check @Module.Projective.of_flat_mittagLeffler

@[stacks 059X "finite-generation companion"]
#check @Module.CountablyGenerated.of_finite
