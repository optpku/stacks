module

public import ReasLib.RingTheory.DirectLimit.RegularLocal
import StacksCheckRecall

/-!
# Directed Colimits of Regular Local Rings

@stack 07DX

The reusable theorem is owned by `Ring.DirectLimit`; this entry records the
Stacks source contract directly.
-/

@[expose] public section

/- Lemma 10.106.8 (Tag 07DX): a directed colimit of regular local rings along
local ring homomorphisms is a regular local ring whenever the colimit is Noetherian. -/
@[stacks 07DX]
#check @Ring.DirectLimit.isRegularLocalRing
