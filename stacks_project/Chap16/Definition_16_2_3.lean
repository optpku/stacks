/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Element.Fin

@[expose] public section

/-!
# Compatibility facade for Definition 16.2.3

The reusable fixed-presentation API is owned by
`ReasLib.RingTheory.Smooth.Standard.Presentation.Fin`, while the generalized
presentation-independent predicates are owned by `Standard.Element.Selected`.
This historical import path remains a public facade for both layers.
-/

/- Definition 16.2.3: elementary standard elements are owned by the
presentation-independent predicate `Algebra.IsElementaryStandard`. -/
@[stacks 07C7 "elementary standard elements"]
#check @Algebra.IsElementaryStandard

/- Definition 16.2.3: strictly standard elements are owned by the
presentation-independent predicate `Algebra.IsStrictlyStandard`. -/
@[stacks 07C7 "strictly standard elements"]
#check @Algebra.IsStrictlyStandard

#check @Algebra.Presentation.IsElementaryStandard
#check @Algebra.Presentation.IsStrictlyStandard
#check @Algebra.IsElementaryStandard.iff_finPresentation
#check @Algebra.IsStrictlyStandard.iff_finPresentation
