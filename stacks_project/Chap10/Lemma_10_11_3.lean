/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
import StacksCheckRecall

/-!
# Lemma 10.11.3

@stack 00HA
-/

@[expose] public section

/- Chap10 Lemma 10 11 3 (Lemma 10.11.3): every module is a filtered colimit of finitely
presented modules. -/
@[stacks 00HA]
#check @ModuleCat.isFinitePresentation_ind
