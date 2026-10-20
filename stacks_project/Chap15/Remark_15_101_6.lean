/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.IdealPower.System

/-!
# Remark 15.101.6

@stack 0EGW
-/

@[expose] public section

open CategoryTheory
open IadicFiniteModuleSystem

/- Remark 15.101.6 (0EGW): finite modules over the rings A / I ^ n form a category.
The reusable owner is the representative presentation and its canonical quotient category in
ReasLib.  The chapter boundary records the source-facing names and keeps no second implementation.
-/

/- Stage and object layer. -/
#check @IadicFiniteModuleSystem.stageRing
@[stacks 0EGW "Remark 15.101.6 (1)"]
#check @IadicFiniteModuleSystem
#check @IadicFiniteModuleSystem.stageIdeal
#check @IadicFiniteModuleSystem.stageIdeal_pow_eq_map
#check @IadicFiniteModuleSystem.powerSubmodule
#check @IadicFiniteModuleSystem.isTorsionByStageIdealPower_iff
#check @IadicFiniteModuleSystem.isTorsionByStageIdealPower_iff_torsionBySet_eq_top
#check @IadicFiniteModuleSystem.torsionQuotient

/- Representative and promotion layer. -/
@[stacks 0EGW "Remark 15.101.6 (2)"]
#check @IadicFiniteModuleSystem.HomRepresentative
#check @IadicFiniteModuleSystem.HomRepresentative.quotientPowerMap
#check @IadicFiniteModuleSystem.HomRepresentative.successor
#check @IadicFiniteModuleSystem.HomRepresentative.promotedLift
#check @IadicFiniteModuleSystem.HomRepresentative.comp
#check @IadicFiniteModuleSystem.HomRepresentative.relation

/- Quotient-category layer. -/
@[stacks 0EGW "Remark 15.101.6 (2)"]
#check @IadicFiniteModuleSystem.Category
#check @IadicFiniteModuleSystem.Category.quotient
#check @IadicFiniteModuleSystem.Category.quotient_obj_as
#check @IadicFiniteModuleSystem.Category.quotient_map_eq_iff
