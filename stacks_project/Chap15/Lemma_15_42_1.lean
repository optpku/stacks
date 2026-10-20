/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Regular.Reduced

/-!
# Lemma 15.42.1

@stack 07QK

The reusable theorem is owned by `RingHom.Regular.isReduced`; the chapter file
records the source label and its two lower-level ingredients.
-/

@[expose] public section

/- Lemma 15.42.1: reducedness ascends along a regular map between Noetherian
rings when the source is reduced. -/
@[stacks 07QK "Lemma 15.42.1: reducedness along a regular map"]
#check @RingHom.Regular.isReduced

#check @RingHom.Regular.isReduced_fiber
#check @RingHom.HasReducedFibers.isReduced_of_flat
