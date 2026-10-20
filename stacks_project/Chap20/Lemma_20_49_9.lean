/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Retracts
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.9: if a binary biproduct of derived `𝒪_X`-modules is perfect, then both
summands are perfect. -/
@[stacks 08CS]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_summands_of_biprod

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_left_of_biprod
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_right_of_biprod
