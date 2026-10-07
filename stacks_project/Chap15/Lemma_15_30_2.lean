module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity

/-!
# Lemma 15.30.2

@stack 062F
-/

@[expose] public section

/- Lemma 15.30.2 (Stacks Lemma 15.30.2), tag `062F`: the list-to-finite-family
bridges are owned by `ReasLib.RingTheory.Sequence.Koszul.Regularity`. -/
@[stacks 062F "weakly regular sequences are Koszul-regular"]
#check @RingTheory.Sequence.IsWeaklyRegular.isKoszulRegularOn

/- Companion for Stacks Lemma 15.30.2, tag `062F`: regular lists use the same
shared bridge. -/
@[stacks 062F "regular sequences are Koszul-regular"]
#check @RingTheory.Sequence.IsRegular.isKoszulRegularOn
