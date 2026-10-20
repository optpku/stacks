/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
import StacksCheckRecall

@[expose] public section

/- Perfectness on a ringed space is definitionally the canonical opens-ringed-site property. -/
#check @AlgebraicGeometry.RingedSpace.CochainComplex.perfect
#check @RingedSite.CochainComplex.perfect
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.perfect
#check @RingedSite.Hom.ModuleDerived.perfect

