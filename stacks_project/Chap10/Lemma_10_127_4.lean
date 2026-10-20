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
# Filtered Colimits from Finitely Presented Algebras

The reusable criterion is owned by `CommAlgCat.Over.FinitePresentation`; this
chapter file retains the textbook entry point and its Stacks tag.

@stack 07C3
-/

-- Lemma 10.127.4, tag `07C3`: selected finitely presented algebras over a
-- target form a filtered colimit precisely when every finitely presented
-- algebra over that target factors through one selected object.
@[stacks 07C3]
#check @CommAlgCat.Over.FinitePresentation.isFilteredColimit_iff_factorization
