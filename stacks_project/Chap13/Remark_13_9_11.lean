/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.DegreewiseSplit.Strictification
import StacksCheckRecall

@[expose] public section

/-!
# Remark 13.9.11

The Stacks Project obtains the obstruction from a ring of dual numbers.  The reusable library
exposes a concrete instance over `ZMod 4`, with `epsilon = 2`, together with its row, chosen
degreewise splitting, three vertical maps, and the homotopy witnessing the left square.  The
existential formulation remains available as a compatibility view of this explicit example.
-/

namespace CochainComplex

@[stacks 014J]
#check @CategoryTheory.ShortComplex.IsMiddleMapStrictifiable
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.row
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.splitting
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.leftMap
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.middleMap
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.rightMap
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.leftHomotopy
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.leftHomotopyComponent_one_zero
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.leftCommSq
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.rightCommSq
@[stacks 014J]
#check @DegreewiseSplit.Strictification.ZModFour.notStrictifiable
@[stacks 014J]
#check @DegreewiseSplit.Strictification.exists_nonStrictifiableMiddleMap

end CochainComplex
