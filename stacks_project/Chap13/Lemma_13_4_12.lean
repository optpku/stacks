/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Pretriangulated.KernelCokernel
import StacksCheckRecall

@[expose] public section

/-
Lemma 13.4.12 is owned by the reusable arrow-category
projection-coprojection normal form and its pretriangulated kernel-cokernel
equivalences. The three checks below are the pairwise, fine-grained form of
the source `TFAE` statement.
-/

@[stacks 05QU] #check @CategoryTheory.Pretriangulated.hasKernel_iff_hasCokernel
#check @CategoryTheory.Pretriangulated.hasKernel_iff_isProjectionThenCoprojection
#check @CategoryTheory.Pretriangulated.hasCokernel_iff_isProjectionThenCoprojection

end
