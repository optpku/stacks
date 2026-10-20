/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Abelian.Extension.ThreeByThree
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.27.7

The reusable owner is the three-by-three extension API.  Its pullback presentation isolates the
diagrammatic content, while the principal theorem identifies existence with vanishing of the
Yoneda product.
-/

/- Lemma 13.27.7 (`0GSM`): the Yoneda product of two composable extension classes vanishes
exactly when they fit into an exact three-by-three diagram. -/
@[stacks 0GSM] #check
  @CategoryTheory.Extension.ThreeByThree.comp_eq_zero_iff_nonempty

/- Companion check: the source-facing exact diagram is reusable independently of `Ext`. -/
@[stacks 0GSM] #check @CategoryTheory.Extension.ThreeByThree
