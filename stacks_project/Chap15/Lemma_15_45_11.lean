/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Henselian.Henselization.DiscreteValuationRing

@[expose] public section

/-!
# Lemma 15.45.11 (0AP3)

@stack 0AP3
-/

-- Lemma 15.45.11: the DVR property of a Noetherian local ring, a
-- henselization, and a strict henselization are equivalent.
@[stacks 0AP3 "Lemma 15.45.11"]
#check @IsHenselizationOf.isDiscreteValuationRing_tfae
