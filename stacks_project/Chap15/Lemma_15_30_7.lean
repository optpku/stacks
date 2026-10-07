module

import StacksCheckRecall
public import ReasLib.RingTheory.Sequence.Koszul.Regularity.Local

/-!
# Koszul regularity over Noetherian local rings

@stack 09CC
-/

@[expose] public section

/- Lemma 15.30.7 (1): the four regularity conditions agree on nonzero finite modules over a
Noetherian local ring when the family lies in the maximal ideal. -/
@[stacks 09CC "Lemma 15.30.7 (1)"]
#check @RingTheory.Sequence.Regularity.local_tfae

/- Lemma 15.30.7 (2): the corresponding four ring-valued regularity conditions agree. -/
@[stacks 09CC "Lemma 15.30.7 (2)"]
#check @RingTheory.Sequence.Regularity.localSequence_tfae
