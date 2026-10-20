/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Local
import StacksCheckRecall

@[expose] public section

/- Perfectness is detected by strictly perfect representatives on an open cover. -/
#check @AlgebraicGeometry.RingedSpace.CochainComplex.isPerfect_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_iff_exists_openCover
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.Perfect.ModelOn

