module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.OverField.Localization

@[expose] public section

/-!
# Localization of Complete Intersections

The source special case `S_g` is covered by the canonical
`IsLocalization.Away g Sg` API below.

@stack 00SA
-/

/- Lemma 10.135.2 (1), tag `00SA`: a global complete intersection over a
field remains a global complete intersection after localization away from one
element. -/
@[stacks 00SA "global complete intersections under localization away"]
#check @IsGlobalCompleteIntersection.of_isLocalizationAway

/- Lemma 10.135.2 (2), tag `00SA`: a local complete intersection over a
field remains a local complete intersection after localization away from one
element. -/
@[stacks 00SA "local complete intersections under localization away"]
#check @IsLocalCompleteIntersection.of_isLocalizationAway

@[stacks 00SA "global complete-intersection localization instance"]
#check @IsGlobalCompleteIntersection.instLocalizationAway
@[stacks 00SA "local complete-intersection localization instance"]
#check @IsLocalCompleteIntersection.instLocalizationAway
