/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Presentation.Fin

@[expose] public section

/- 16.2.3.2: the elementary-standard tail equations are the intrinsic tail
relation condition of the chosen finite presentation. -/
@[stacks 07C9]
#check @Algebra.Presentation.tailRelationCondition

#check @Fin.natAdd_castLEEmb
#check @Algebra.Presentation.leadingRelationIdeal
#check @Algebra.Presentation.tailRelationCondition_iff_sigma
#check @Algebra.Presentation.IsElementaryStandard
