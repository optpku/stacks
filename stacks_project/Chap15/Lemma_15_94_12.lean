/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.AdicCompletion.Reduced
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 15.94.12 (0G5V)

@stack 0G5V
-/

/- Lemma 15.94.12 (Stacks `0G5V`): a reduced ring which is derived complete with respect to a
finitely generated ideal `I` is `I`-adically complete. -/
@[stacks 0G5V "Lemma 15.94.12, adic completeness of a reduced derived-complete ring"]
#check @ModuleCat.IsDerivedCompleteWithRespectTo.isAdicComplete_of_isReduced
