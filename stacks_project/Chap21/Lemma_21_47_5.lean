/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Pullback
import StacksCheckRecall

@[expose] public section

/- Lemma 21.47.5 (08H6): total derived pullback along a morphism of ringed sites preserves
perfect derived module sheaves. -/
@[stacks 08H6]
#check @RingedSite.Hom.modulePullbackDerived_isPerfect

#check @RingedSite.Hom.modulePullbackPerfect
#check @RingedSite.Hom.modulePullbackPerfectCompιIso
