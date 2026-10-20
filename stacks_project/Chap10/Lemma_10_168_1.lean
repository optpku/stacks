/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Flat
public import ReasLib.RingTheory.DirectLimit.FlatModel
public import ReasLib.RingTheory.RingHom.FinitePresentation.FlatModel
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.168.1 [stacks 02JO]: canonical recall.  The reusable owners are
`RingHom.FlatModel.exists_overInt`, `Ring.DirectLimit.FlatModel.exists_atStage`,
and `Ring.DirectLimit.Algebra.Approximation.ModuleSystem.eventually_flat`.

@stack 02JO
-/
@[stacks 02JO]
#check @RingHom.FlatModel.exists_overInt

/- Lemma 10.168.1 (2) [stacks 02JO]: canonical recall.  The reusable owner is
`Ring.DirectLimit.FlatModel.exists_atStage`. -/
@[stacks 02JO]
#check @Ring.DirectLimit.FlatModel.exists_atStage

/- Lemma 10.168.1 (3) [stacks 02JO]: canonical recall.  The reusable owner is
`Ring.DirectLimit.Algebra.Approximation.ModuleSystem.eventually_flat`. -/
@[stacks 02JO]
#check @Ring.DirectLimit.Algebra.Approximation.ModuleSystem.eventually_flat
