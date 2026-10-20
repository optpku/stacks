/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Sheaf.Yoneda

import StacksCheckRecall

@[expose] public section

/-!
[stacks 00Z8]

Definition 7.47.10 recalls `Presheaf.IsSheaf`; the coverwise Yoneda formulation is its reusable
characterization.
-/

@[stacks 00Z8] #check CategoryTheory.Presheaf.IsSheaf
#check CategoryTheory.Presheaf.isSheaf_iff_forall_yonedaSheafCondition
