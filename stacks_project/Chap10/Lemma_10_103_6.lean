/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Surjective
import StacksCheckRecall

/-!
# Cohen--Macaulay modules under a surjective scalar map

@stack 0AAD
-/

@[expose] public section

/- Lemma 10.103.6: Cohen--Macaulayness is unchanged after restricting scalars along a
surjective homomorphism of Noetherian local rings.  The canonical owner is stronger than the
source statement: it does not need a separate finite-module hypothesis. -/
@[stacks 0AAD]
#check @Module.CohenMacaulay.iff_restrictScalars_of_surjective
