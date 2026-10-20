/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Catenary.FiniteType
import StacksCheckRecall

/-!
# Lemma 10.105.5
@stack 0ECE

The essentially-finite-type stability theorem is owned by
`ReasLib.RingTheory.Catenary.FiniteType`.
-/

/- Lemma 10.105.5: an essentially finite type algebra over a universally catenary
Noetherian ring is universally catenary. -/
@[stacks 0ECE]
#check @universallyCatenaryRing_of_essFiniteType
