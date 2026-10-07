module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Presentation.Fin

@[expose] public section

/- 16.2.3.4: the strict-standard tail equations use the same intrinsic tail
relation condition as elementary standardness. -/
@[stacks 07ES]
#check @Algebra.Presentation.tailRelationCondition

#check @Fin.natAdd_castLEEmb
#check @Algebra.Presentation.leadingRelationIdeal
#check @Algebra.Presentation.tailRelationCondition_iff_sigma
#check @Algebra.Presentation.IsStrictlyStandard
