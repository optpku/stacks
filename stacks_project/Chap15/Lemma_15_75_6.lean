/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Termwise
import StacksCheckRecall

/-!
# Bounded complexes with perfect terms

Lemma 15.75.6 states that a bounded cochain complex of perfect modules is perfect in the derived
category.  The reusable statement is owned by ReasLib.

@stack 066T
-/

@[expose] public section

-- Lemma 15.75.6 (066T): a bounded complex of perfect modules is a perfect complex.
@[stacks 066T "Lemma 15.75.6"]
#check @CochainComplex.Bounded.isPerfect
