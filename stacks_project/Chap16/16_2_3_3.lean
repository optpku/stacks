/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Presentation.Fin

@[expose] public section

/- 16.2.3.3: the strict-standard Jacobian expansion uses the column minors of
the chosen finite presentation. -/
@[stacks 07ER]
#check @Algebra.Presentation.jacobianColumnMinor

#check @Set.powersetCard.initial
#check @Algebra.Presentation.IsStrictlyStandard
