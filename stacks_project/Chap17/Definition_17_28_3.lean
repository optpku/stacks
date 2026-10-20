/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Differentials
import StacksCheckRecall

@[expose] public section

/- Definition 17.28.3 (08RP): the module of relative differentials and its universal derivation
are owned on an arbitrary ringed site and specialize to sheaves on a topological space. -/
@[stacks 08RP]
#check @SheafOfModules.RingedSite.relativeDifferentials

#check @SheafOfModules.RingedSite.relativeDifferential
#check @TopCat.Sheaf.relativeDifferentials
#check @TopCat.Sheaf.relativeDifferential
