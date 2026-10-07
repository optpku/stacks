module

public import ReasLib.RingTheory.Localization.Away.InjectiveAtPrime
import StacksCheckRecall

@[expose] public section

/-!
# Injective principal neighborhoods of a prime localization

@stack 0BX1
-/

@[stacks 0BX1 "unit support owner"]
#check @IsLocalization.map_units

/- Lemma 10.31.9: one principal neighborhood maps injectively to the prime localization under the
source finiteness or reducedness hypotheses. -/
@[stacks 0BX1]
#check
  @Localization.AtPrime.exists_awayMap_injective
