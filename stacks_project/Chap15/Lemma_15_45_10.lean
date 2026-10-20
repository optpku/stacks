/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.Regular

@[expose] public section

/-!
# Lemma 15.45.10 (06LN)

@stack 06LN
-/

-- Lemma 15.45.10: regularity of a Noetherian local ring, a
-- henselization, and a strict henselization are equivalent.
@[stacks 06LN "Lemma 15.45.10"]
#check @IsHenselizationOf.isRegularLocalRing_tfae

-- Pairwise views of the same regularity comparison.
#check @IsHenselizationOf.isRegularLocalRing_iff
#check @IsStrictHenselizationOf.isRegularLocalRing_iff
