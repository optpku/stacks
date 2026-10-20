/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.17.16

The reusable K-flat cycles theorem and its kernel view live in ReasLib.  This chapter entry only
recalls the source-facing specialization.
-/

/- Lemma 21.17.16 (0G7C): the cycles of an acyclic, termwise-flat K-flat complex of module
sheaves on a ringed site are flat. -/
@[stacks 0G7C]
#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.isFlat_cycles

#check @SheafOfModules.RingedSite.CochainComplex.IsKFlat.isFlat_kernel_dFrom
#check @HomologicalComplex.IsKFlat.isFlat_cycles
