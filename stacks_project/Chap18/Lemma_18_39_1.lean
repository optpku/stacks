/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 18.39.1: pullback along a morphism of ringed sites preserves flat module sheaves. -/
@[stacks 05VD]
#check @SheafOfModules.RingedSite.IsFlat.modulePullback
