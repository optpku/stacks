/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.Maps
import StacksCheckRecall

/-!
# Krull Dimension Under Going Up and Going Down

The ring-level dimension inequality is the canonical `RingHom` specialization
of the topological Krull-dimension comparison.

@stack 00OH
-/

@[expose] public section

/- Lemma 10.112.1 (Stacks tag `00OH`): a spectrally surjective ring map
satisfying going up or going down cannot decrease Krull dimension. -/
@[stacks 00OH]
#check @RingHom.ringKrullDim_le_of_comap_surjective_of_specializing_or_generalizing
