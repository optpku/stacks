module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.CohenMacaulay

@[expose] public section

/-!
# Lemma 15.45.9 (06LM)

@stack 06LM
-/

-- Lemma 15.45.9: the Cohen-Macaulay property of a Noetherian local
-- ring, a henselization, and a strict henselization are equivalent.
@[stacks 06LM "Lemma 15.45.9"]
#check @IsHenselizationOf.cohenMacaulay_tfae

-- Pairwise views of the same Cohen-Macaulay comparison.
#check @IsHenselizationOf.cohenMacaulay_iff
#check @IsStrictHenselizationOf.cohenMacaulay_iff
