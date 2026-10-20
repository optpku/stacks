/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution.PureExt
public import stacks_project.Chap46.Definition_46_8_8_PureInjectiveResolution

@[expose] public section

/- The canonical pure-extension API remains available to source-facing resolution users. -/
#check ModuleCat.PureInjectiveCoresolution.cochainComplex
#check ModuleCat.PureInjectiveCoresolution.homComplex
#check ModuleCat.PureInjectiveCoresolution.pureExt
