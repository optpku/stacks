module

import StacksCheckRecall
public import ReasLib.RingTheory.DividedPowers.Category.Colimits

@[expose] public section

open CategoryTheory.Limits

universe u

/- Lemma 23.3.4 (Tag 07GX): the category of divided power rings has all colimits. -/
@[stacks 07GX]
#check (DividedPowerRing.hasColimits : HasColimits DividedPowerRing.{u})
