module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Smooth

import StacksCheckRecall

@[expose] public section

/-! [stacks 0H6Z (1)]
Smooth covers admit the reusable selected-etale-refinement API. -/
@[stacks 0H6Z "(1)"] #check @AlgebraicGeometry.Scheme.Etale.smoothCover_refinedByEtale

/-! [stacks 0H6Z (2)]
The reverse selected-site continuity failure is a reusable counterexample. -/
@[stacks 0H6Z "(2)"] #check @AlgebraicGeometry.Scheme.Etale.exists_smoothToEtale_not_continuous
