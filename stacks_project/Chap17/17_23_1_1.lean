/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Annihilator.Stalk
import StacksCheckRecall

@[expose] public section

/- Equation 17.23.1.1 (0H2I): the ideal in `𝒪_{X,x}` obtained from the stalk of
`Ann(F)` is contained in the annihilator ideal of `F_x`. -/
@[stacks 0H2I "Equation 17.23.1.1"]
#check @SheafOfModules.Annihilator.stalkIdeal_le

/- The left-hand side is owned as an image ideal of a canonical map into the stalk ring. -/
#check @SheafOfModules.Annihilator.stalkToRing
#check @SheafOfModules.Annihilator.stalkIdeal
#check @SheafOfModules.Annihilator.mem_stalkIdeal_iff

/- Germ and elementwise forms expose the mathematical content of the inclusion. -/
#check @SheafOfModules.Annihilator.stalkToRing_germ
#check @SheafOfModules.Annihilator.stalkImage_smul_eq_zero
#check @SheafOfModules.Annihilator.germ_mem_moduleAnnihilator
