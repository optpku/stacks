/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Normal.Nagata.Smooth
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.164.7

@stack 0354
-/

/- Lemma 10.164.7 [stacks 0354]: canonical recall of Nagata descent along a
smooth algebra map which is surjective on prime spectra. -/
@[stacks 0354]
#check @NagataRing.of_smooth_of_specComap_surjective
