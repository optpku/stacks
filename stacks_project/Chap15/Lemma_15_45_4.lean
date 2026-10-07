module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.Reduced

@[expose] public section

/-!
# Lemma 15.45.4 (06DH)

@stack 06DH
-/

-- Lemma 15.45.4: a local ring, a henselization, and a strict
-- henselization are reduced simultaneously.
@[stacks 06DH "Lemma 15.45.4"]
#check @IsHenselizationOf.isReduced_tfae

-- Pairwise views of the same reducedness comparison.
#check @IsHenselizationOf.isReduced_iff
#check @IsStrictHenselizationOf.isReduced_iff
