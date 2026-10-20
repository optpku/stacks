/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Limit.ProIsomorphism
import StacksCheckRecall

/-!
# Lemma 15.87.6

@stack 0H9L
-/

@[expose] public section

open CategoryTheory

/- Lemma 15.87.6 (Stacks 0H9L): a pro-isomorphism of sequential systems induces a
non-canonical isomorphism between chosen derived limits.  The reusable statement is owned by
`IsDerivedLimit.existsIso_of_proIso`; this chapter entry is only the source-labelled recall. -/
@[stacks 0H9L]
#check @CategoryTheory.IsDerivedLimit.existsIso_of_proIso

#check @CategoryTheory.IsDerivedLimit
#check @CategoryTheory.Pro.lim
