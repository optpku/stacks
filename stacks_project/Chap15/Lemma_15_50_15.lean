module

public import ReasLib.RingTheory.Henselian.PairHenselization.GRing
import StacksCheckRecall

/-!
# Lemma 15.50.15

@stack 0AH3
-/

@[expose] public section

/- Lemma 15.50.15, tag `0AH3`: a henselization along an ideal of a G-ring is again a G-ring. -/
@[stacks 0AH3]
#check @IsPairHenselization.isGRing
