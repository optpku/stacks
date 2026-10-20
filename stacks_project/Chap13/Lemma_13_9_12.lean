/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.Exactness
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.9.12

The exactness argument through a termwise split middle row is owned by the neutral
`HomotopyCategory.DegreewiseSplit.Exactness` leaf.  The canonical API consumes the choice-free
`ShortComplex.IsDegreewiseSplit` property; selected-family, pointwise, and admissible-short-exact
bridges remain visible.
-/

namespace CochainComplex

@[stacks 086L]
#check @DegreewiseSplit.HomotopyCategory.comp_zero_of_splitting
@[stacks 086L]
#check @DegreewiseSplit.HomotopyCategory.comp_zero
@[stacks 086L]
#check @DegreewiseSplit.HomotopyCategory.comp_zero_of_termwise
@[stacks 086L]
#check @DegreewiseSplit.HomotopyCategory.comp_zero_of_admissible

end CochainComplex
