/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.ChaoticCohomology
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 21.43.11 (0GZR): on a chaotic ringed site with flat restriction morphisms,
canonical derived quasi-coherence agrees with quasicoherence of every cohomology module
sheaf. -/
@[stacks 0GZR]
#check @ModulesOnCategory.Chaotic.isQuasiCoherent_eq_cohomologyIn

#check @ModulesOnCategory.Chaotic.mem_iff_cohomology_isQuasicoherent
