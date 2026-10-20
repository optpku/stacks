/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Regularity.Permutable
import StacksCheckRecall

/-!
# Lemma 10.68.10

@stack 07DW
-/

@[expose] public section

/-
Lemma 10.68.10 (Stacks tag `07DW`) is a chapter-facing recall of the
permutable-regular-sequence API.  The shared owner separates the
module-valued permutation/sublist criterion from the self-module polynomial
comparison.
-/

@[stacks 07DW]
#check @RingTheory.Sequence.IsRegular.perm_sublist_mvPolynomial_tfae
