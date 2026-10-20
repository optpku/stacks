/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ShortComplex.UniversallyExact.Criteria
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.82.4

@stack 058L
-/

/- Lemma 10.82.4, tag `058L`, is a canonical recall: for a short complex of `R`-modules whose
last term is finitely presented, universal exactness is equivalent to the existence of a
splitting.  The reusable criterion is
`CategoryTheory.ShortComplex.UniversallyExact.iff_nonempty_splitting`. -/
@[stacks 058L "universal exactness and splitting"]
#check @CategoryTheory.ShortComplex.UniversallyExact.iff_nonempty_splitting
