module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import StacksCheckRecall

/-!
# Regular Rings

@stack 00OD
-/

@[expose] public section

/- Definition 10.110.7 (Stacks tag `00OD`): a Noetherian ring is regular if
every localization at a prime ideal is a regular local ring. -/
@[stacks 00OD]
#check @IsRegularRing

/- The constructor/eliminator form of the same prime-local definition. -/
@[stacks 00OD "prime-local characterization"]
#check @isRegularRing_iff
