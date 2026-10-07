module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Retraction

@[expose] public section

/- Lemma 16.3.3: a syntomic algebra admits a smooth retract extension which is
flat and a relative global complete intersection over the original base. -/
@[stacks 07CG]
#check @Algebra.RetractExtension.RelativeCI.nonempty

#check @Algebra.RetractExtension.RelativeCI
#check @Algebra.RetractExtension.RelativeCI.spec
#check @Algebra.RetractExtension.Smoothing.toRelativeCI
#check @Algebra.RetractExtension.retract
