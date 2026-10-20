/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Algebra.SplitPolynomialPresentation
import StacksCheckRecall

/-!
# Split polynomial presentations after finite free base change

Lemma 15.21.3 is owned by
`Algebra.exists_finiteFree_baseChange_surjective_splitPolynomialQuotient`.  The owner keeps the
explicit split relation family and the surjective map to the canonical base change `R' ⊗[R] S`.

@stack 0531
-/

@[stacks 0531 "Lemma 15.21.3"]
#check @Algebra.exists_finiteFree_baseChange_surjective_splitPolynomialQuotient
