/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.FinitePresentation
import StacksCheckRecall

@[expose] public section

/-!
# Finitely Presented Algebras over a Target

The category and canonical colimit cocone are shared `CommAlgCat` API; this
file retains the textbook entry point.

@stack 0BUF
-/

-- Lemma 10.127.1, tag `0BUF`: finitely presented `R`-algebras over `A`
-- form a filtered category, and their canonical cocone has colimit `A`.
@[stacks 0BUF]
#check @CommAlgCat.Over.FinitePresentation.isFilteredColimit
