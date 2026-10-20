/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Pair.Local
import StacksCheckRecall

/-!
# Pair Henselization of a local ring

This file recalls Lemma 15.12.3 from the reusable pair-Henselization API.

@stack 0A03
-/

@[expose] public section

-- Lemma 15.12.3: pair Henselization at the maximal ideal is local-ring Henselization.
@[stacks 0A03 "Lemma 15.12.3"]
#check @localRing_henselization_isHenselizationOf

@[stacks 0A03 "canonical local-ring Henselization instance"]
#check @localRing_henselization.instIsHenselizationOf
