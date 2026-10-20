/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
import StacksCheckRecall

@[expose] public section

/- 20.3.0.4: bounded-below derived direct image and its cohomology use the canonical
ringed-space owners. -/
@[stacks 0718 "20.3.0.4: bounded-below derived direct image"]
#check @AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus

@[stacks 0718 "20.3.0.4: bounded-below derived direct-image cohomology"]
#check @AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus.cohomology
