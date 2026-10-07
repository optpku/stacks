module

public import ReasLib.RingTheory.Sequence.Regularity.Localization
import StacksCheckRecall

/-!
# Spreading a regular sequence from a prime localization

@stack 061L
-/

@[expose] public section

/- Lemma 10.68.6 (061L): a sequence that is regular on `M` after localization
at a prime is regular on `M` over some principal open containing that prime. -/
@[stacks 061L]
#check @RingTheory.Sequence.IsRegular.exists_away_of_atPrime
