/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RegularLocalRing.Completion
import StacksCheckRecall

/-!
Lemma 15.43.4 (07NY): a Noetherian local ring is regular if and only if its completion is
regular.

@stack 07NY
-/

@[expose] public section

universe u

open IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/- Lemma 15.43.4 (07NY), using the canonical maximal-ideal completion owner. -/
@[stacks 07NY]
#check
  (isRegularLocalRing_iff_isRegularLocalRing_maximalIdeal_adicCompletion A :
    IsRegularLocalRing A ↔
      IsRegularLocalRing (AdicCompletion (maximalIdeal A) A))
