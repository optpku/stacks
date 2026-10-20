/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
import StacksCheckRecall

@[expose] public section

/- Definition 20.49.1 (1): perfect complexes of `𝒪_X`-modules are owned by the reusable
ringed-space facade. -/
@[stacks 08CM "(1)"]
#check @AlgebraicGeometry.RingedSpace.CochainComplex.IsPerfect

/- Definition 20.49.1 (2): perfect objects of `D(𝒪_X)` are owned by the reusable
ringed-space facade. -/
@[stacks 08CM "(2)"]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect

#check @AlgebraicGeometry.RingedSpace.ModuleDerived.isPerfect_iff_exists_representative
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.exists_representative
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.of_iso_q_obj

