/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Retraction

@[expose] public section

/- Lemma 16.3.4: a smooth algebra admits a smooth retract extension which is
standard smooth over the original base. -/
@[stacks 07CH]
#check @Algebra.RetractExtension.StandardSmooth.nonempty

#check @Algebra.RetractExtension.StandardSmooth
#check @Algebra.RetractExtension.StandardSmooth.spec
#check @Algebra.RetractExtension.retract
