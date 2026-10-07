module

public import ReasLib.RingTheory.Kaehler.Quotient
import StacksCheckRecall

/-!
# Lemma 10.131.9

@stack 00RU
-/

@[expose] public section

/- Lemma 10.131.9 [stacks 00RU]: canonical recall.  The source's conormal
sequence is represented by the kernel-identified map
`KaehlerDifferential.Quotient.conormalToBaseChange`; exactness is separated
from the standard mathlib surjectivity statement for the Kähler base-change
map. -/
@[stacks 00RU]
#check @KaehlerDifferential.Quotient.conormalToBaseChange
#check @KaehlerDifferential.Quotient.conormalToBaseChange_toCotangent
#check @KaehlerDifferential.Quotient.conormalToBaseChange_exact
#check @KaehlerDifferential.mapBaseChange_surjective
