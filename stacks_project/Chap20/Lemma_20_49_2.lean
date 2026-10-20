/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Local
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.2 (1): strictly perfect representatives on an open cover imply perfectness. -/
@[stacks 08CN "(1)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_of_isOpenCover

/- Lemma 20.49.2 (2): every complex representing a perfect derived module is perfect. -/
@[stacks 08CN "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.of_representation

