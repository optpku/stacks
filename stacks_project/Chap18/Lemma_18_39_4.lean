/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.Flat
import StacksCheckRecall

@[expose] public section

/- Lemma 18.39.4: module pullback preserves a short exact sequence whose quotient is flat. -/
@[stacks 0G6R]
#check @RingedSite.Hom.map_shortExact_of_flat_X₃
