/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.InverseLimit
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.11.12 (0EM6)

@stack 0EM6
-/

/- Lemma 15.11.12, Stacks `0EM6`: a compatible inverse system of henselian pairs is henselian
after taking its inverse limit. -/
@[stacks 0EM6 "Lemma 15.11.12, inverse limit of henselian pairs"]
#check @HenselianRing.inverseLimit
