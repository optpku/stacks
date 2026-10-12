/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Presentation.Fin

@[expose] public section

/- 16.2.3.1: the elementary-standard Jacobian equation uses the leading
Jacobian determinant of the chosen finite presentation. -/
@[stacks 07C8]
#check @Algebra.Presentation.leadingJacobianDet

#check @Algebra.Presentation.jacobianMatrix
#check @Set.powersetCard.initial
#check @Algebra.Presentation.IsElementaryStandard
