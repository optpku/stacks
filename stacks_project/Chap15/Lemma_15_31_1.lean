module

import StacksCheckRecall
public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.KoszulRegular

/-!
# Lemma 15.31.1

@stack 0G6L
-/

@[expose] public section

/- Lemma 15.31.1, tag `0G6L`: a Koszul-regular finite family makes the extended
alternating Cech complex cohomologically concentrated in its top degree. -/
@[stacks 0G6L "Lemma 15.31.1"]
#check @LocalizedModule.Away.Cech.Alternating.Cohomology.isZero_of_isKoszulRegularSequence

#check @LocalizedModule.Away.Cech.Alternating.extended
#check @RingTheory.Sequence.IsKoszulRegularSequence
