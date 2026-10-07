module

public import ReasLib.RingTheory.Kaehler.JacobiZariski
import StacksCheckRecall

/-!
# Lemma 10.139.2

@stack 06A8

The split conormal sequence for a smooth map is the formally smooth splitting criterion together
with the canonical implication from smoothness to formal smoothness.
-/

@[expose] public section

@[stacks 06A8 "split conormal sequence"]
#check @KaehlerDifferential.mapBaseChange_has_section_of_formallySmooth

@[stacks 06A8 "smooth implies formally smooth"]
#check @Algebra.Smooth.formallySmooth
