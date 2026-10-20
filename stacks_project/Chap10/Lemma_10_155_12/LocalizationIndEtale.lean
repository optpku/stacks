/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.LocalRing.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Local-ring localization recall

This former helper duplicated the neutral local-ring localization theorem and
registered it globally as an instance.  Consumers should install the shared
theorem locally only when an instance is genuinely required.

@stack 08HV
-/

@[stacks 08HV]
#check @IsLocalRing.isLocalization_primeCompl_maximalIdeal
