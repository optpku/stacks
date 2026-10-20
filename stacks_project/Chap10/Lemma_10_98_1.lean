/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.InverseSystem
import StacksCheckRecall

/-!
# Lemma 10.98.1

@stack 0G1Q
-/

@[expose] public section

/- Lemma 10.98.1 (0G1Q): the inverse limit of a positive system of modules
annihilated stagewise by `I ^ n` is `I`-adically complete when `I` is finitely
generated.  The quotient-factorization and retract API belongs to the shared
positive adic inverse-system leaf. -/
@[stacks 0G1Q]
#check @CategoryTheory.PNatInverseSystem.isAdicComplete_limit_of_stagewise_annihilated

@[stacks 0G1Q "limit projection to a quotient stage"]
#check @CategoryTheory.PNatInverseSystem.limitProjectionQuotient

@[stacks 0G1Q "completion-to-limit map"]
#check @CategoryTheory.PNatInverseSystem.completionToLimit
