/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Filtration.Cohomology
import StacksCheckRecall

@[expose] public section

/-!
# Equation 12.24.5.1

Compatibility facade for the explicit ModuleCat presentation of the filtration induced on the
cohomology of a two-step complex.
-/

/- Equation 12.24.5.1 [012R]: the source quotient of filtered cycles plus boundaries is the
canonical stage of the induced cohomology filtration. -/
@[stacks 012R]
#check @ModuleCat.FilteredCohomology.Stage.induced

#check @ModuleCat.FilteredCohomology.Stage.step
#check @ModuleCat.FilteredCohomology.Stage.stageSubmodule
#check @ModuleCat.FilteredCohomology.Stage.stepEquivFiltration
