module

public import ReasLib.RingTheory.Flatness.MittagLeffler.Colimit
import StacksCheckRecall

/-!
# Directed colimits of Mittag-Leffler modules

@stack 0AS7
-/

@[expose] public section

/- Lemma 10.89.9 (Tag 0AS7): a directed colimit of Mittag-Leffler modules along universally
injective transition maps is Mittag-Leffler. -/
@[stacks 0AS7]
#check @Module.MittagLeffler.colimit_of_universallyInjective
