/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.HigherDirectImage.Colimits
import StacksCheckRecall

@[expose] public section

/- Lemma 21.16.4 (0H7B): the local covering criterion for the canonical colimit comparison of a
higher direct image is the reusable site-level theorem below. -/
@[stacks 0H7B]
#check @CategoryTheory.Sheaf.HigherDirectImage.colimitComparison_isIso_of_cover
