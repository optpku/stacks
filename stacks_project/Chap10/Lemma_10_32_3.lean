module

public import ReasLib.RingTheory.Ideal.LocallyNilpotent
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.32.3

@stack 0544

The reusable owner is `Ideal.IsLocallyNilpotent.map`; the historical chapter
statement is recalled directly instead of being re-exported under a chapter name.
-/

@[stacks 0544 "extension of a locally nilpotent ideal"]
#check @Ideal.IsLocallyNilpotent.map
