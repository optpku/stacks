module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.Depth

@[expose] public section

/-!
# Lemma 15.45.8 (06LL)

@stack 06LL
-/

-- Lemma 15.45.8 (1): a Noetherian local ring and a henselization
-- have the same depth.
@[stacks 06LL "Lemma 15.45.8 (1)"]
#check @IsHenselizationOf.moduleDepth_eq

-- Lemma 15.45.8 (2): a Noetherian local ring and a strict
-- henselization have the same depth.
@[stacks 06LL "Lemma 15.45.8 (2)"]
#check @IsStrictHenselizationOf.moduleDepth_eq
