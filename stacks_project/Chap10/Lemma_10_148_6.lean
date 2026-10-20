/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.FormallyUnramified.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 10.148.6

@stack 07QE
-/

@[expose] public section

/- Lemma 10.148.6 [stacks 07QE]: canonical recall.  The reusable owner is
`RingHom.FormallyUnramified.of_isColimit`; its canonical
`isStableUnderFilteredColimits` instance also supplies the generic morphism-
property interface. -/
@[stacks 07QE]
#check @RingHom.FormallyUnramified.of_isColimit
