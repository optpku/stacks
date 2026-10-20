/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RegularLocalRing.Defs
import StacksCheckRecall

/-!
# Regular Rings

@stack 00OD
-/

@[expose] public section

/- Definition 10.110.7 (Stacks tag `00OD`): a Noetherian ring is regular if
every localization at a prime ideal is a regular local ring. -/
@[stacks 00OD]
#check @IsRegularRing

/- The constructor/eliminator form of the same prime-local definition. -/
@[stacks 00OD "prime-local characterization"]
#check @isRegularRing_iff
