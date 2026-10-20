/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.CyclicFiltration
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.5.4

@stack 00KZ
-/

/- Lemma 10.5.4 (Tag 00KZ): a finite module admits a finite filtration whose
successive quotients are quotients of the base ring.  The reusable relation,
filtration object, and existence theorem are owned by `ReasLib`. -/
@[stacks 00KZ] #check @Submodule.IsQuotientEquivQuotient
@[stacks 00KZ] #check @Submodule.isQuotientEquivQuotient_sup_span
@[stacks 00KZ] #check @Module.CyclicFiltration
@[stacks 00KZ] #check @Module.CyclicFiltration.successiveQuotient
@[stacks 00KZ] #check @Module.exists_finite_cyclic_filtration
