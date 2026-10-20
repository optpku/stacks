/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Cech
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.2: a covering family of a quasi-compact site object has a finite subfamily whose
augmented Čech sequence remains exact. -/
@[stacks 0G1W]
#check @CategoryTheory.Coverage.QuasiCompactObject.existsFiniteCechExact

/- The stronger sieve-saturated specialization remains available for topology-level clients. -/
#check @SheafOfModules.Localization.Cech.exists_finset_exact_and_epi
