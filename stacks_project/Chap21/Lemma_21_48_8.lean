/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

/- Lemma 21.48.8 (0A0A): internal Hom from a sequential homotopy colimit of perfect derived
module sheaves is the homotopy limit of the canonical dual-tensor inverse system. -/
@[stacks 0A0A]
#check @RingedSite.Hom.ModuleDerived.IsPerfect.homotopyLimit_dualTensor_of_homotopyColimit

#check @CategoryTheory.MonoidalClosed.Dual.tensorTower
#check @CategoryTheory.MonoidalClosed.Dual.tensorTower_obj
#check @CategoryTheory.MonoidalClosed.Dual.tensorTower_transitionMap
#check @CategoryTheory.HomotopyColimit.IsOf.dualTensor
