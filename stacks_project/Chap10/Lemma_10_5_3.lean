/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Module.FinitePresentation.Exact

@[expose] public section

/-!
# Exact-Sequence Finiteness Recall

The five source clauses are exposed by the existing `Module.Finite` and
`Module.FinitePresentation` exact-sequence owners.

@stack 0519
-/

/- Lemma 10.5.3 (1): finite outer terms in an exact right-exact sequence imply
finite middle term. -/
@[stacks 0519 "(1) finite middle term from finite outer terms"]
#check @Module.Finite.of_exact

/- Lemma 10.5.3 (2): finite presentation of the two outer terms implies finite
presentation of the middle term. -/
@[stacks 0519 "(2) finite presentation of the middle term"]
#check @Module.finitePresentation_of_exact

/- Lemma 10.5.3 (3): a finite middle term gives a finite quotient in a
surjective sequence. -/
@[stacks 0519 "(3) finite quotient term"]
#check @Module.Finite.of_surjective

/- Lemma 10.5.3 (4): finite presentation of the middle term and finiteness of
the kernel source imply finite presentation of the quotient. -/
@[stacks 0519 "(4) finite presentation of the quotient"]
#check @Module.finitePresentation_of_surjective_of_exact

/- Lemma 10.5.3 (5): a finitely presented quotient and finite middle term give
a finite kernel. -/
@[stacks 0519 "(5) finite kernel term"]
#check @Module.Finite.of_exact_of_finitePresentation
