/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Replacement
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.7 (09QN): a finite composable row has an admissibly monic replacement whose
vertical comparison is componentwise a homotopy equivalence. -/
@[stacks 09QN]
#check Comp.HomotopyReplacement.exists_admissibleMono

/- The witness-refined replacement retaining every homotopy retract. -/
#check Comp.HomotopyReplacement.exists_withRetracts
