/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Criteria
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.1 (04ES): the local-unit, finite unit-ideal, and binary-factorization criteria are
equivalent. -/
@[stacks 04ES]
#check @Sheaf.localUnit_tfae

#check @Sheaf.localUnitDichotomy_iff_finiteUnitIdealCover
#check @Sheaf.localUnitDichotomy_iff_binaryFactorizationMap_locallySurjective
#check @Sheaf.finiteUnitIdealCover_iff_binaryFactorizationMap_locallySurjective
