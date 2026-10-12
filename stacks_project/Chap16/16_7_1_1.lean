/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Presentation.BaseRing

@[expose] public section

/- Lemma 16.7.1.1 (tag 07CS): the base-ring presentation bridge is owned by
ReasLib. -/

@[stacks 07CS]
#check @Algebra.Presentation.TailRelationCondition.iff_baseRing

@[stacks 07CS]
#check @Algebra.IsStrictlyStandard.Presentation.exists_baseRing_tail
