/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 18.40.4 (04EU): a locally ringed commutative-ring sheaf has local nontriviality
and local unit dichotomy. -/
@[stacks 04EU]
#check @Sheaf.IsLocallyRinged

#check @Sheaf.LocalUnitDichotomy
#check @Sheaf.isLocallyRinged_of_conditions
