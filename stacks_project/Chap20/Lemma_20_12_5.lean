/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
import StacksCheckRecall

@[expose] public section

/- Lemma 20.12.5 (09T0): if an `𝒪_X`-module is flasque, then all of its positive
higher direct images vanish. -/
@[stacks 09T0]
#check @AlgebraicGeometry.RingedSpace.Hom.HigherDirectImage.isZero_of_flasque
