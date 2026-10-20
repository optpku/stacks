/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Truncation.EventualHomology
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.11.5

The lower, upper, and two-sided truncation replacements are owned by the neutral
`CochainComplex.Truncation.EventualHomology` support leaf.  This chapter file is only the labeled
recall surface.
-/

namespace CochainComplex

@[stacks 05RV]
#check @Truncation.GE.exists_of_eventually_isZero
@[stacks 05RV]
#check @Truncation.LE.exists_of_eventually_isZero
@[stacks 05RV]
#check @Truncation.Bounded.exists_of_eventually_isZero

@[stacks 05RV]
#check @Truncation.Bounded.IsReplacement

end CochainComplex
