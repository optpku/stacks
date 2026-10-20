/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.IntegralClosure.FiniteSubalgebra
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.36.4 (Tag 00GM): finite sets of integral elements lie in finite subalgebras.

@stack 00GM
-/

-- The canonical owner retains the finite-set hypothesis and the exact existential conclusion.
@[stacks 00GM]
#check @Algebra.forall_isIntegral_iff_exists_finite_subalgebra

@[stacks 00GM "finite adjoin criterion"]
#check @Algebra.finite_adjoin_iff_of_finite

@[stacks 00GM "finite integral adjoin"]
#check @Algebra.finite_adjoin_of_finite_of_isIntegral
