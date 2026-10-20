/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.CohomologicalDimensionAnalogue
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme.CoherentFormalModules


/- Remark 52.22.6 (1): the analogue of Proposition 52.22.4 with the
cohomological-dimension bound in place of the finite-generator hypothesis. -/
@[stacks 0EJQ] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.cohomologicalDimensionAnalogue_extends : Prop)

/- Remark 52.22.6 (2): the corresponding completion analogue under adic
completeness. -/
@[stacks 0EJQ] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.cohomologicalDimensionAnalogue_isCompletion : Prop)

end AlgebraicGeometry.Scheme.CoherentFormalModules
