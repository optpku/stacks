/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

/- Example 21.48.6 (0FPU): for a perfect derived module sheaf `K`, the canonical closed dual,
coevaluation, and evaluation form `ExactPairing K (MonoidalClosed.dual K)`. -/
@[stacks 0FPU]
#check @CategoryTheory.MonoidalClosed.Dual.exactPairing

#check @RingedSite.Hom.ModuleDerived.IsPerfect.isIso_tensorIhomUnitToEnd
#check @CategoryTheory.MonoidalClosed.Dual.coevaluation
#check @CategoryTheory.MonoidalClosed.Dual.evaluation
#check @CategoryTheory.MonoidalClosed.Dual.coevaluation_comp_tensorComparison
#check @CategoryTheory.MonoidalClosed.Dual.exactPairing_coevaluation
#check @CategoryTheory.MonoidalClosed.Dual.exactPairing_evaluation
