module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.OverField.CohenMacaulay

@[expose] public section

/-!
# Cohen-Macaulay Local Complete Intersections

The source theorem is the direct consequence of the intrinsic local
complete-intersection predicate recorded below.

@stack 00SB
-/

/- Lemma 10.135.3, tag `00SB`: a local complete intersection over a field is
a Cohen-Macaulay ring. -/
@[stacks 00SB "local complete intersections over a field are Cohen-Macaulay"]
#check @IsLocalCompleteIntersection.cohenMacaulayRing
