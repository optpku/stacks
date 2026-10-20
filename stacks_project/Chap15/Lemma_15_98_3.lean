/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.DerivedTower.Perfect

@[expose] public section

/-!
# Lemma 15.98.3

@stack 0CQG
-/

/-!
# Perfect limits over inverse systems of rings

The reusable owner for Lemma 15.98.3 is independent of chapter files and uses the canonical
`DerivedTower`, `HomotopyLimit.IsOf`, and presented base-change map APIs.
-/

/- Lemma 15.98.3 (1) (0CQG): under the surjectivity, local-nilpotence,
all-stages-or-nilpotent-tail, and Cartesian hypotheses, the homotopy limit is perfect. -/
@[stacks 0CQG "Lemma 15.98.3 (1), perfect inverse limit"]
#check @CategoryTheory.ModuleCat.DerivedTower.Perfect.limit

/- Lemma 15.98.3 (2) (0CQG): the canonical derived base-change map from the presented limit to
every stage is an isomorphism. -/
@[stacks 0CQG "Lemma 15.98.3 (2), perfect inverse-limit base change"]
#check @CategoryTheory.ModuleCat.DerivedTower.Perfect.Limit.baseChangeMap_isIso
