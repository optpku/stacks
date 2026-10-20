/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.TopologyComparison.Consequences
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.30.8

The bounded-below derived consequences of Situation `21.30.1` are owned by ReasLib.  The chapter
entry is a recall facade with one check for each independent source clause.
-/

open CategoryTheory
open CategoryTheory.GrothendieckTopology.TopologyComparison

/- Lemma 21.30.8 (0EZF), clause (1): `(V_n)` holds for every `n`. -/
@[stacks 0EZF "(1)"]
#check @Vanishing.localVanishing_all

/- Lemma 21.30.8 (0EZF), clause (2): the bounded-below comparison unit is an isomorphism on
`D⁺[A' X]`. -/
@[stacks 0EZF "(2)"]
#check @Consequences.unit_isIso_of_cohomologyIn

/- Lemma 21.30.8 (0EZF), clause (3): bounded-below direct image preserves `A'`-cohomology. -/
@[stacks 0EZF "(3)"]
#check @Consequences.pushforward_mem_cohomologyIn

/- Lemma 21.30.8 (0EZF), clause (4): bounded-below topology-comparison base change is invertible
in the Situation. -/
@[stacks 0EZF "(4)"]
#check @Consequences.baseChange_isIso_of_allVanishing

end
