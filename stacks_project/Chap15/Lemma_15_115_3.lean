module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.BaseChange.FormalSmooth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.115.3

Formal smoothness after finite DVR base change is owned by ReasLib.  This source-facing file keeps
the official tag and a direct recall; its path retains the legacy chapter numbering. The current
Stacks entry is Lemma 15.116.3.

@stack 09EQ
-/

@[stacks 09EQ "Lemma 15.115.3: formal smoothness after finite DVR base change"]
#check @DVR.Field.BaseChange.formallySmoothAt
