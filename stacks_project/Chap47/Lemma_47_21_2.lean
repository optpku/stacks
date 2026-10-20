/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.Gorenstein.CohenMacaulay
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.21.2: A Gorenstein ring is Cohen-Macaulay. -/
@[stacks 0DW8] #check
  (IsGorensteinRing.instCohenMacaulayRing :
    ∀ (R : Type u) [CommRing R] [IsGorensteinRing R], CohenMacaulayRing R)
