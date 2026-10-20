/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
import StacksCheckRecall

/-!
# Definition 18.31.3

Relative flatness is owned by `SheafOfModules.RingedSite.IsFlatOver`; the owner spells out
restriction of scalars along the inverse-image structure map without chapter-local notation.
-/

@[expose] public section

/- Definition 18.31.3 (08M5): a module on the source is flat over the target. -/
@[stacks 08M5]
#check @SheafOfModules.RingedSite.IsFlatOver
