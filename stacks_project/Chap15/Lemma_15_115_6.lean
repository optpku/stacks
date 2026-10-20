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
# Lemma 15.115.6

The repository path retains the legacy numbering.  The current Stacks entry is Lemma 15.116.6,
tag `0EXV`; the reusable field-model owner is `DVR.Field.IsTamelyRamified`.

@stack 0EXV
-/

/- Lemma 15.115.6: tameness descends in a finite separable tower. -/
@[stacks 0EXV "Lemma 15.115.6: tame ramification descends in a finite separable tower"]
#check @DVR.Field.IsTamelyRamified.ofTower
