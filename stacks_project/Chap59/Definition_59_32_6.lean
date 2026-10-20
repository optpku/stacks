/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.Henselian.StrictHenselian
import StacksCheckRecall

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

/- Definition 59.32.6: a local ring is strictly henselian when it is henselian
and its residue field is separably closed. -/
@[stacks 03QK] #check (StrictHenselianLocalRing R : Prop)
