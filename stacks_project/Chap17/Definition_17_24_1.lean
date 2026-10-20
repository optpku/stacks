/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Monoid
import StacksCheckRecall

/-!
# Definition 17.24.1 compatibility entry point

The topology-independent `SheafOfModules.RingedSite.Koszul` owner is already the correct
formalization layer. Its component API identifies the graded algebra with exterior powers and
characterizes the differential as the unique derivation extending the original degree-one map.
-/

@[expose] public section

/- Definition 17.24.1 (062K): the Koszul complex of `phi : F ⟶ 𝒪_X` is the commutative
differential graded algebra whose underlying graded algebra is the exterior algebra of `F`, with
the unique derivation restricting to `phi` in degree one. -/
@[stacks 062K]
#check @SheafOfModules.RingedSite.Koszul.commMon

#check @SheafOfModules.RingedSite.Koszul.commMon_X
#check @SheafOfModules.RingedSite.Koszul.commMon_one_component
#check @SheafOfModules.RingedSite.Koszul.commMon_mul_component
#check @SheafOfModules.RingedSite.Koszul.differential_degreeOne
#check @SheafOfModules.RingedSite.Koszul.differential_isDerivation
#check @SheafOfModules.RingedSite.Koszul.differential_unique
