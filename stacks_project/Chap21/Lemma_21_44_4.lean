/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.StrictlyPerfect
import StacksCheckRecall

@[expose] public section

/-! Lemma 21.44.4 is the intrinsic ringed-site pullback theorem. -/

@[stacks 08H3]
#check @RingedSite.Hom.modulePullbackComplex.isStrictlyPerfect
