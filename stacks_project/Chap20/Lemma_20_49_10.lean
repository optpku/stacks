/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.OpenPushforward
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.10: a perfect derived module on an open subspace remains perfect under derived
open pushforward when its cohomology has support closed in the ambient ringed space. -/
@[stacks 08DP]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.pushforwardFromOpen_of_isSupportedOn
