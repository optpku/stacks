/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.FieldTheory.Minpoly.Charpoly
import StacksCheckRecall

@[expose] public section

/- Lemma 9.20.2 (Tag 0BIG): for a finite field extension, the characteristic polynomial of
`Algebra.lmul K L α` is `(minpoly K α) ^ finrank K⟮α⟯ L`. -/
@[stacks 0BIG]
#check Algebra.charpoly_lmul_eq_minpoly_pow_finrank_adjoin
