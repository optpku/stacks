/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.GRing
import StacksCheckRecall

/-!
# Definition 15.50.1

@stack 07GH
-/

@[expose] public section

/- Definition 15.50.1: G-rings and completed localizations are owned by the
reusable regular-ring-map layer. -/
@[stacks 07GH]
#check @IsGRing

#check @PrimeSpectrum.CompletedLocalRing
#check @PrimeSpectrum.completedLocalMap
#check @isGRing_iff_forall_regular_localization_completion
