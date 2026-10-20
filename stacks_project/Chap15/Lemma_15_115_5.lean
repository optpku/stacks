/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Tame
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.115.5

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.116.5,
tag `0EXU`.  The branchwise tame condition and its tower composition theorem are owned by
`DVR.Field.IsTamelyRamified`.

@stack 0EXU
-/

/- Lemma 15.115.5 (1): branchwise tame hypothesis on the upper integral closure. -/
@[stacks 0EXU "Lemma 15.115.5: branchwise tame hypothesis"]
#check @DVR.Field.IsTamelyRamified.IsTamelyRamifiedOnTower

/- Lemma 15.115.5 (2): tame ramification composes in the integral-closure tower. -/
@[stacks 0EXU "Lemma 15.115.5: tame ramification composes"]
#check @DVR.Field.IsTamelyRamified.ofTameOnIntegralClosureTower
