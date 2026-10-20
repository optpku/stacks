/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Smooth.Standard.Locus

@[expose] public section

/- Lemma 16.2.2: for a fixed presentation, a smooth point admits selected
variable and relation subsets defining an elementary standard neighborhood. -/
@[stacks 07C6]
#check @Algebra.SmoothAtPrime.exists_isElementaryFor

/- Presentation-independent consequences used by later smoothing arguments. -/
#check @Algebra.SmoothAtPrime.exists_not_mem_elementaryStandard
#check @Algebra.SmoothAtPrime.exists_not_mem_strictlyStandard
